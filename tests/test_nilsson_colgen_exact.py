"""Column generation rests on exact arithmetic and on proofs, never on an optimiser's report.

``z3.Optimize`` is not a certificate: on the pricing objective of
:mod:`unicode_logic_kit.prob._column_gen` it has been seen to return a world that does not
maximise, with a value that is not the value of that world, and different answers for
identical inputs in one interpreter. So the module only PROPOSES a world with it, evaluates
the world exactly, and settles "no world improves" by evaluating every world exactly (few
atoms) or by an unsatisfiable solver query (many atoms). These tests pin that, with
expectations derived by hand:

* the problem ``P(A) = 7/10``, ``P(B | ¬A) = 1`` — consistent, and ``P(¬B) ∈ [0, 7/10]``,
  ``P(B) ∈ [3/10, 1]`` — asked in every order of its questions, in a fresh interpreter;
* a pricing call whose four world values are worked out below, with an optimiser that lies;
* an exact vertex enumeration of the polytope as an oracle that shares no code with the
  kit, on seeded random problems;
* the stop of the phase-2 loop, which needs the primal value and the dual objective to agree.
"""

import itertools
import os
import random
import subprocess
import sys
import textwrap
from fractions import Fraction as F

import pytest

import unicode_logic_kit
from unicode_logic_kit import api
from unicode_logic_kit.fol.nodes import And, Atom, Iff, Implies, Not, Or, Xor
from unicode_logic_kit.prob import _column_gen
from unicode_logic_kit.prob.nilsson import ProbConstraint, entailment_bounds


def f(text):
    return api.parse_any(text).formula


# The problem: P(A) = 7/10 and P(B | ¬A) = 1.
#
# Worlds over (A, B): pAB, pAnB, pnAB, pnAnB. P(B | ¬A) = 1 with P(¬A) = 3/10 > 0 forces
# pnAnB = 0, hence pnAB = 3/10 and pAB + pAnB = 7/10. So the set is consistent
# (pAB = 7/10 or pAnB = 7/10), P(¬B) = pAnB ranges over [0, 7/10] and P(B) = pAB + 3/10
# over [3/10, 1].
QUESTIONS = {"B ↔ ⊥": (F(0), F(7, 10)), "¬B": (F(0), F(7, 10)), "B": (F(3, 10), F(1))}


def seven_tenths_problem():
    return [ProbConstraint(f("A"), F(7, 10), F(7, 10)),
            ProbConstraint(f("B"), F(1), F(1), given=f("¬A"))]


_FRESH_INTERPRETER = textwrap.dedent("""
    import sys
    from fractions import Fraction as F
    from unicode_logic_kit import api
    from unicode_logic_kit.prob import ProbConstraint, entailment_bounds

    def parse(text):
        return api.parse_any(text).formula

    constraints = [ProbConstraint(parse("A"), F(7, 10), F(7, 10)),
                   ProbConstraint(parse("B"), F(1), F(1), given=parse("¬A"))]
    for question in sys.argv[1:]:
        try:
            bounds = entailment_bounds(constraints, parse(question), strategy="column_generation")
            print(question, bounds.lower, bounds.upper)
        except ValueError as exc:
            print(question, "ValueError", str(exc)[:60])
""")


class TestEveryOrderOfQuestions:
    @pytest.mark.parametrize("order", list(itertools.permutations(QUESTIONS)), ids=" | ".join)
    def test_fresh_interpreter(self, order):
        package_root = os.path.dirname(os.path.dirname(os.path.abspath(unicode_logic_kit.__file__)))
        env = dict(os.environ)
        env["PYTHONPATH"] = os.pathsep.join(filter(None, [package_root, env.get("PYTHONPATH")]))
        env["PYTHONIOENCODING"] = "utf-8"
        run = subprocess.run([sys.executable, "-c", _FRESH_INTERPRETER, *order], env=env,
                             capture_output=True, text=True, encoding="utf-8", timeout=300)
        assert run.returncode == 0, run.stderr
        expected = [f"{q} {QUESTIONS[q][0]} {QUESTIONS[q][1]}" for q in order]
        assert run.stdout.strip().splitlines() == expected

    def test_one_process_every_order(self):
        # The questions of one problem, asked one after the other in this process, in every order, with
        # the pricing as the module ships it.
        for order in itertools.permutations(QUESTIONS):
            for question in order:
                bounds = entailment_bounds(seven_tenths_problem(), f(question), strategy="column_generation")
                assert (bounds.lower, bounds.upper) == QUESTIONS[question], (order, question)

    @pytest.mark.parametrize("exhaustive_up_to", [6, 0], ids=["exact-enumeration", "z3-solver-query"])
    def test_one_process_both_pricing_paths(self, monkeypatch, exhaustive_up_to):
        monkeypatch.setattr(_column_gen, "_EXHAUSTIVE_PRICING_MAX_ATOMS", exhaustive_up_to)
        for order in itertools.permutations(QUESTIONS):
            for question in order:
                bounds = entailment_bounds(seven_tenths_problem(), f(question), strategy="column_generation")
                assert (bounds.lower, bounds.upper) == QUESTIONS[question], (order, question)


# ---------------------------------------------------------------------------
# One pricing call, worked out by hand.
# ---------------------------------------------------------------------------

class TestPricingIsExact:
    """The rows of the 7/10 problem, in order, are

        r0:  1{A}                   >= 7/10
        r1: -1{A}                   >= -7/10
        r2:  1{B ∧ ¬A} - 1{¬A}      >= 0
        r3:  1{¬A} - 1{B ∧ ¬A}      >= 0

    and for ``y = (1, 0, 1, 0)``, ``λ = 1`` and cost 0 the reduced cost of a world is
    ``1 + 1{A} + 1{B ∧ ¬A} − 1{¬A}``:  (A,B) = (F,F): 1+0+0-1 = 0;  (F,T): 1+0+1-1 = 1;
    (T,F): 1+1+0-0 = 2;  (T,T): 1+1+0-0 = 2.
    """

    ATOMS = ["A", "B"]
    Y = [F(1), F(0), F(1), F(0)]
    LAM = F(1)
    TABLE = {(False, False): F(0), (False, True): F(1), (True, False): F(2), (True, True): F(2)}

    @staticmethod
    def _parts():
        rows = _column_gen._build_rows(seven_tenths_problem())
        cost_of = _column_gen._ZERO_COST
        cost_z3 = _column_gen._ZERO_COST_Z3
        return rows, cost_of, cost_z3

    @pytest.mark.parametrize("exhaustive_up_to", [6, 0], ids=["exact-enumeration", "z3-solver-query"])
    def test_the_value_is_the_exact_value_of_the_world_returned(self, monkeypatch, exhaustive_up_to):
        monkeypatch.setattr(_column_gen, "_EXHAUSTIVE_PRICING_MAX_ATOMS", exhaustive_up_to)
        rows, cost_of, cost_z3 = self._parts()
        found, world, value = _column_gen._price(self.ATOMS, rows, self.Y, self.LAM, cost_of, cost_z3)
        assert found is True
        assert value > 0
        assert value == self.TABLE[(world["A"], world["B"])]

    def test_exact_enumeration_returns_the_maximiser(self, monkeypatch):
        monkeypatch.setattr(_column_gen, "_EXHAUSTIVE_PRICING_MAX_ATOMS", 6)
        rows, cost_of, cost_z3 = self._parts()
        found, world, value = _column_gen._price(self.ATOMS, rows, self.Y, self.LAM, cost_of, cost_z3)
        assert (found, value) == (True, F(2))
        assert world == {"A": True, "B": False}  # the first of the two worlds of value 2

    @pytest.mark.parametrize("proposal", ["worst", "none"])
    def test_a_proposal_that_does_not_improve_is_not_believed(self, monkeypatch, proposal):
        # The optimiser proposes the world of value 0 (or no world at all): the solver query
        # still finds a world with a positive value, and the exact value is reported.
        monkeypatch.setattr(_column_gen, "_EXHAUSTIVE_PRICING_MAX_ATOMS", 0)
        answer = {"worst": {"A": False, "B": False}, "none": None}[proposal]
        monkeypatch.setattr(_column_gen, "_propose_world", lambda *args, **kwargs: answer)
        rows, cost_of, cost_z3 = self._parts()
        found, world, value = _column_gen._price(self.ATOMS, rows, self.Y, self.LAM, cost_of, cost_z3)
        assert found is True
        assert value == self.TABLE[(world["A"], world["B"])] > 0

    @pytest.mark.parametrize("exhaustive_up_to", [6, 0], ids=["exact-enumeration", "z3-solver-query"])
    def test_no_world_improves_a_zero_dual(self, monkeypatch, exhaustive_up_to):
        # y = 0, λ = 0, cost 0: every world has reduced cost 0, so none is positive.
        monkeypatch.setattr(_column_gen, "_EXHAUSTIVE_PRICING_MAX_ATOMS", exhaustive_up_to)
        monkeypatch.setattr(_column_gen, "_propose_world",
                            lambda *args, **kwargs: {"A": True, "B": True})  # an optimiser's guess
        rows, cost_of, cost_z3 = self._parts()
        found, world, value = _column_gen._price(self.ATOMS, rows, [F(0)] * 4, F(0), cost_of, cost_z3)
        assert (found, world, value) == (False, None, F(0))

    def test_a_wide_problem_is_not_enumerated(self, monkeypatch):
        # 30 atoms: 2**30 worlds. Pricing must neither enumerate them nor stop early.
        # P(S0) >= 1/2 is the only row with a nonzero multiplier; a world with S0 true has
        # reduced cost y0 * 1 + λ = 1 + 0 > 0, so the answer is "found", reached with a
        # handful of coefficient evaluations.
        atoms = [f"S{i}" for i in range(30)]
        rows = _column_gen._build_rows([ProbConstraint(Atom("S0", ()), F(1, 2), F(1))])
        calls = []

        def counting(row):
            def coeff_of(world):
                calls.append(1)
                if len(calls) > 5000:
                    raise AssertionError("the pricing step evaluated far more worlds than a search needs")
                return row.coeff_of(world)
            return _column_gen._Row(coeff_of, row.z3_coeff, row.rhs, row.label)

        counted = [counting(r) for r in rows]
        found, world, value = _column_gen._price(
            atoms, counted, [F(1), F(0)], F(0), _column_gen._ZERO_COST, _column_gen._ZERO_COST_Z3)
        assert found is True and value == 1 and world["S0"] is True
        assert len(calls) < 100


# ---------------------------------------------------------------------------
# What a stop rests on: the certificates.
# ---------------------------------------------------------------------------

class TestStopsRestOnCertificates:
    def test_a_dual_that_is_not_optimal_is_never_turned_into_a_bound(self, monkeypatch):
        # Phase 2 gets y = 0, λ = -1: feasible for the restricted dual (the cost of every
        # world is >= 0 > -1) and violated by NO world, so pricing finds nothing and the
        # loop would stop. Its objective is -1, whereas the minimum of P(¬B) is 0 (see the
        # module problem): the primal value 0 differs from the dual objective -1, the
        # optimum is not certified, and the answer is a refusal, not the number.
        real = _column_gen._solve_dual

        def degraded(rows, columns, cost_of, y_upper_bound=None):
            if y_upper_bound is None:
                return [F(0)] * len(rows), F(-1)
            return real(rows, columns, cost_of, y_upper_bound)

        monkeypatch.setattr(_column_gen, "_solve_dual", degraded)
        with pytest.raises(ValueError, match="could not certify"):
            entailment_bounds(seven_tenths_problem(), f("¬B"), strategy="column_generation")

    def test_a_solver_that_denies_feasibility_cannot_produce_an_inconsistency_verdict(self, monkeypatch):
        # The module problem is consistent. If the solver answered "no distribution over
        # these columns" even when one exists, the restricted dual has value 0, which is no
        # Farkas certificate (that needs a positive value): the answer is a refusal that
        # names the failed certification, never "probabilistically inconsistent".
        monkeypatch.setattr(_column_gen, "_has_feasible_distribution", lambda rows, columns: False)
        with pytest.raises(ValueError, match="could not certify") as caught:
            entailment_bounds(seven_tenths_problem(), f("¬B"), strategy="column_generation")
        assert "probabilistically inconsistent" not in str(caught.value)

    def test_a_dual_that_bounds_more_than_a_feasible_distribution_costs_is_refused(self, monkeypatch):
        # Weak duality: no distribution costs less than the objective of a dual that no world violates.
        # Here "no world violates" is claimed for y = 0, λ = 10 (objective 10), while the exact value of
        # the primal witness, a probability, is at most 1. The two cannot both be right.
        monkeypatch.setattr(_column_gen, "_solve_dual",
                            lambda rows, columns, cost_of, y_upper_bound=None: ([F(0)] * len(rows), F(10)))
        monkeypatch.setattr(_column_gen, "_price", lambda *args, **kwargs: (False, None, F(0)))
        rows, columns, cost_of = self._one_atom_master()
        with pytest.raises(ValueError, match="weak duality"):
            _column_gen._phase2(["A"], rows, columns, cost_of, lambda av: None, True, 10)

    def test_a_world_that_improves_and_is_already_a_column_is_refused(self, monkeypatch):
        # The dual was verified for every column, so no column can have a positive reduced cost.
        monkeypatch.setattr(_column_gen, "_price", lambda *args, **kwargs: (True, {"A": True}, F(1)))
        rows, columns, cost_of = self._one_atom_master()
        with pytest.raises(ValueError, match="already a column"):
            _column_gen._phase2(["A"], rows, columns, cost_of, lambda av: None, True, 10)
        # phase 1 starts from the world A = False alone, which cannot give P(A) >= 3/10
        monkeypatch.setattr(_column_gen, "_price", lambda *args, **kwargs: (True, {"A": False}, F(1)))
        with pytest.raises(ValueError, match="already a column"):
            _column_gen._phase1(["A"], rows, [{"A": False}], 10, [])

    def test_a_world_the_solver_calls_improving_that_is_not_is_refused(self, monkeypatch):
        # y = 0, λ = 0 and no cost: every world has reduced cost 0, so none improves. A solver that
        # hands back the world (A, B) = (T, T) as one that does is contradicted by evaluating it.
        monkeypatch.setattr(_column_gen, "_EXHAUSTIVE_PRICING_MAX_ATOMS", 0)
        monkeypatch.setattr(_column_gen, "_propose_world", lambda *args, **kwargs: None)
        monkeypatch.setattr(_column_gen, "_find_violating_world",
                            lambda *args, **kwargs: {"A": True, "B": True})
        rows = _column_gen._build_rows(seven_tenths_problem())
        with pytest.raises(ValueError, match="evaluating that world exactly"):
            _column_gen._price(["A", "B"], rows, [F(0)] * 4, F(0), _column_gen._ZERO_COST,
                               _column_gen._ZERO_COST_Z3)

    @staticmethod
    def _one_atom_master():
        rows = _column_gen._build_rows([ProbConstraint(f("A"), F(3, 10), F(6, 10))])
        columns = [{"A": False}, {"A": True}]
        return rows, columns, (lambda w: F(1) if w["A"] else F(0))

    def test_a_primal_that_is_not_a_distribution_is_refused(self, monkeypatch):
        # Weights (2, 2) are read back from the optimiser: they do not sum to 1.
        rows, columns, cost_of = self._one_atom_master()
        monkeypatch.setattr(_column_gen, "_z3_to_fraction", lambda value: F(2))
        with pytest.raises(ValueError, match="could not certify"):
            _column_gen._solve_restricted_primal(rows, columns, cost_of)

    def test_a_feasible_distribution_is_verified_before_phase_one_accepts_it(self, monkeypatch):
        rows, columns, _cost_of = self._one_atom_master()
        monkeypatch.setattr(_column_gen, "_z3_to_fraction", lambda value: F(2))
        with pytest.raises(ValueError, match="could not certify"):
            _column_gen._has_feasible_distribution(rows, columns)

    def test_a_dual_with_a_negative_multiplier_is_refused(self, monkeypatch):
        rows, columns, cost_of = self._one_atom_master()
        monkeypatch.setattr(_column_gen, "_z3_to_fraction", lambda value: F(-1))
        with pytest.raises(ValueError, match="could not certify"):
            _column_gen._solve_dual(rows, columns, cost_of)

    def test_a_dual_that_violates_a_row_is_refused(self, monkeypatch):
        # y = (5, 5), λ = 5: the row of the world A=False reads 0*5 + 0*5 + 5 <= cost 0, false.
        rows, columns, cost_of = self._one_atom_master()
        monkeypatch.setattr(_column_gen, "_z3_to_fraction", lambda value: F(5))
        with pytest.raises(ValueError, match="could not certify"):
            _column_gen._solve_dual(rows, columns, cost_of)

    @pytest.mark.parametrize("proposal", ["seed", "none"])
    def test_an_inconsistent_set_is_refused_with_an_optimiser_that_proposes_nothing_useful(
            self, monkeypatch, proposal):
        # P(A) >= 4/5 and P(¬A) >= 4/5 cannot both hold: they sum to more than 1.
        monkeypatch.setattr(_column_gen, "_EXHAUSTIVE_PRICING_MAX_ATOMS", 0)
        answer = {"seed": {"A": False}, "none": None}[proposal]
        monkeypatch.setattr(_column_gen, "_propose_world", lambda *args, **kwargs: answer)
        constraints = [ProbConstraint(f("A"), F(4, 5), F(1)), ProbConstraint(f("¬A"), F(4, 5), F(1))]
        with pytest.raises(ValueError, match="probabilistically inconsistent"):
            entailment_bounds(constraints, f("A"), strategy="column_generation")

    @pytest.mark.parametrize("proposal", ["seed", "none"])
    def test_a_consistent_set_is_not_called_inconsistent_by_a_useless_optimiser(
            self, monkeypatch, proposal):
        monkeypatch.setattr(_column_gen, "_EXHAUSTIVE_PRICING_MAX_ATOMS", 0)
        answer = {"seed": {"A": False, "B": False}, "none": None}[proposal]
        monkeypatch.setattr(_column_gen, "_propose_world", lambda *args, **kwargs: answer)
        for question, expected in QUESTIONS.items():
            bounds = entailment_bounds(seven_tenths_problem(), f(question), strategy="column_generation")
            assert (bounds.lower, bounds.upper) == expected


# ---------------------------------------------------------------------------
# An oracle that shares no code with the kit: exact vertex enumeration.
# ---------------------------------------------------------------------------

_TRUE_NAMES = ("$true", "⊤")
_FALSE_NAMES = ("$false", "⊥")


def _holds(formula, world):
    if isinstance(formula, Atom):
        if formula.predicate in _TRUE_NAMES:
            return True
        if formula.predicate in _FALSE_NAMES:
            return False
        return world[formula.predicate]
    if isinstance(formula, Not):
        return not _holds(formula.formula, world)
    left, right = _holds(formula.left, world), _holds(formula.right, world)
    if isinstance(formula, And):
        return left and right
    if isinstance(formula, Or):
        return left or right
    if isinstance(formula, Implies):
        return (not left) or right
    if isinstance(formula, Iff):
        return left == right
    assert isinstance(formula, Xor)
    return left != right


def _names(formula, out):
    if isinstance(formula, Atom):
        if formula.predicate not in _TRUE_NAMES + _FALSE_NAMES:
            out.add(formula.predicate)
    elif isinstance(formula, Not):
        _names(formula.formula, out)
    else:
        _names(formula.left, out)
        _names(formula.right, out)


def _solve_square(matrix, rhs):
    """Gauss-Jordan over Fractions; the solution, or ``None`` when the matrix is singular."""
    n = len(matrix)
    work = [row[:] + [b] for row, b in zip(matrix, rhs)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if work[r][col] != 0), None)
        if pivot is None:
            return None
        work[col], work[pivot] = work[pivot], work[col]
        scale = work[col][col]
        work[col] = [x / scale for x in work[col]]
        for r in range(n):
            if r != col and work[r][col] != 0:
                factor = work[r][col]
                work[r] = [x - factor * y for x, y in zip(work[r], work[col])]
    return [work[i][n] for i in range(n)]


def vertex_bounds(constraints, conclusion):
    """``(min, max)`` of P(conclusion) over {p >= 0, Σp = 1, constraints}, by enumerating
    the vertices (basic feasible solutions) of the polytope; ``None`` if it is empty."""
    names = set()
    for c in constraints:
        _names(c.formula, names)
        if c.given is not None:
            _names(c.given, names)
    _names(conclusion, names)
    names = sorted(names)
    worlds = [dict(zip(names, bits)) for bits in itertools.product((False, True), repeat=len(names))]
    count = len(worlds)

    def indicator(formula):
        return [F(1) if _holds(formula, w) else F(0) for w in worlds]

    # rows: (coefficients over the worlds, "=" or "<=", right-hand side)
    rows = [([F(1)] * count, "=", F(1))]
    for c in constraints:
        if c.given is None:
            ind = indicator(c.formula)
            if c.lower == c.upper:
                rows.append((ind, "=", c.lower))
            else:
                if c.lower > 0:
                    rows.append(([-x for x in ind], "<=", -c.lower))
                if c.upper < 1:
                    rows.append((ind, "<=", c.upper))
        else:
            given = indicator(c.given)
            both = [F(1) if (_holds(c.formula, w) and _holds(c.given, w)) else F(0) for w in worlds]
            if c.lower == c.upper:
                rows.append(([b - c.lower * g for b, g in zip(both, given)], "=", F(0)))
            else:
                rows.append(([b - c.upper * g for b, g in zip(both, given)], "<=", F(0)))
                rows.append(([c.lower * g - b for b, g in zip(both, given)], "<=", F(0)))
    slack = sum(1 for r in rows if r[1] == "<=")
    width = count + slack
    matrix, rhs, used = [], [], 0
    for coeffs, kind, bound in rows:
        row = list(coeffs) + [F(0)] * slack
        if kind == "<=":
            row[count + used] = F(1)
            used += 1
        matrix.append(row)
        rhs.append(bound)
    # drop linearly dependent rows; a dependent row with a different right-hand side: empty
    kept, reduced = [], []
    for i, row in enumerate(matrix):
        v = row[:] + [rhs[i]]
        for pivot, r in reduced:
            if v[pivot] != 0:
                factor = v[pivot] / r[pivot]
                v = [x - factor * y for x, y in zip(v, r)]
        pivot = next((j for j in range(width) if v[j] != 0), None)
        if pivot is None:
            if v[width] != 0:
                return None
            continue
        reduced.append((pivot, v))
        kept.append(i)
    matrix = [matrix[i] for i in kept]
    rhs = [rhs[i] for i in kept]
    objective = indicator(conclusion) + [F(0)] * slack
    low = high = None
    for basis in itertools.combinations(range(width), len(kept)):
        solution = _solve_square([[matrix[i][j] for j in basis] for i in range(len(kept))], rhs)
        if solution is None or any(x < 0 for x in solution):
            continue
        value = sum(objective[j] * x for j, x in zip(basis, solution))
        low = value if low is None or value < low else low
        high = value if high is None or value > high else high
    return None if low is None else (low, high)


def _random_formula(rng, depth, atoms):
    if depth == 0 or rng.random() < 0.25:
        kind = rng.random()
        if kind < 0.3:
            return Atom(rng.choice(_TRUE_NAMES), ())
        if kind < 0.5:
            return Atom(rng.choice(_FALSE_NAMES), ())
        return Atom(rng.choice(atoms), ())
    op = rng.choice(["not", "and", "or", "implies", "iff", "xor"])
    if op == "not":
        return Not(_random_formula(rng, depth - 1, atoms))
    cls = {"and": And, "or": Or, "implies": Implies, "iff": Iff, "xor": Xor}[op]
    return cls(_random_formula(rng, depth - 1, atoms), _random_formula(rng, depth - 1, atoms))


def _random_problem(rng):
    atoms = ["A", "B", "C"][: rng.randint(1, 3)]
    probabilities = [F(0), F(1), F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(1, 5), F(7, 10)]
    constraints = []
    for _ in range(rng.randint(0, 3)):
        formula = _random_formula(rng, rng.randint(0, 3), atoms)
        given = _random_formula(rng, rng.randint(0, 2), atoms) if rng.random() < 0.3 else None
        a, b = rng.choice(probabilities), rng.choice(probabilities)
        low, high = min(a, b), max(a, b)
        if rng.random() < 0.5:
            low = high
        constraints.append(ProbConstraint(formula, low, high, given=given))
    return constraints, _random_formula(rng, rng.randint(0, 3), atoms)


def _kit_bounds(constraints, conclusion, strategy):
    try:
        bounds = entailment_bounds(constraints, conclusion, strategy=strategy)
    except ValueError as exc:
        assert "probabilistically inconsistent" in str(exc), exc
        return None
    return bounds.lower, bounds.upper


class TestAgainstVertexEnumeration:
    def test_hand_checked_oracle(self):
        # The oracle itself, on the module problem and on an empty polytope.
        assert vertex_bounds(seven_tenths_problem(), f("¬B")) == (F(0), F(7, 10))
        assert vertex_bounds(seven_tenths_problem(), f("B")) == (F(3, 10), F(1))
        empty = [ProbConstraint(f("A"), F(4, 5), F(1)), ProbConstraint(f("¬A"), F(4, 5), F(1))]
        assert vertex_bounds(empty, f("A")) is None

    @pytest.mark.parametrize("exhaustive_up_to", [6, 0], ids=["exact-enumeration", "z3-solver-query"])
    def test_seeded_random_problems(self, monkeypatch, exhaustive_up_to):
        monkeypatch.setattr(_column_gen, "_EXHAUSTIVE_PRICING_MAX_ATOMS", exhaustive_up_to)
        empty = 0
        for seed in range(120):
            constraints, conclusion = _random_problem(random.Random(seed))
            expected = vertex_bounds(constraints, conclusion)
            empty += expected is None
            assert _kit_bounds(constraints, conclusion, "column_generation") == expected, seed
            assert _kit_bounds(constraints, conclusion, "direct") == expected, seed
        assert 10 < empty < 110  # the generator reaches both the empty and the non-empty polytopes
