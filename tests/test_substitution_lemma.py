r"""Capture-avoiding substitution, checked against the substitution lemma by brute force.

``substitute(φ, x, t)`` is correct when, for every structure and every assignment ``g``,

    ⟦φ[x := t]⟧_g  =  ⟦φ⟧_{g[x ↦ ⟦t⟧_g]}                                  (value lemma)

and its free variables are exactly

    fv(φ) \ {x}   plus   fv(t) when x is free in φ                           (free-variable lemma).

The oracle is a Tarski evaluator written in this file (it shares nothing with the kit's
evaluators) and a generator of random formulas over a name pool that is small on purpose: the
binder, the target and the replacement's variables are drawn from the same four names, so a
binder that has to be renamed meets a target of the fresh name's own spelling all the time.

The defect the first group of tests pins: a binder renamed away from a free variable of the
replacement was given a name that avoided the replacement and the body but not the TARGET, so
the new binder could be spelled like the target and was then substituted away. For
``∀x1 P(x1)`` with ``x0 := x1`` the binder ``x1`` captures the incoming ``x1``; the first free
name of its shape is ``x0``, the target's own spelling; the renamed matrix ``P(x0)`` then has
its ``x0`` replaced by ``x1``, and the result ``∀x0 P(x1)`` has a free variable the input does
not have. Every branch that renames a binder had it: the quantifier, the sorted quantifier,
the three counting binders and the cardinality terms, the slashed existential and the lambda.
"""

import itertools
import random
import types

import pytest

from unicode_fol_kit.atp.fitch import _subst_var
from unicode_fol_kit.fol.lambda_tools import eliminate_lambdas
from unicode_fol_kit.fol.nodes import (
    And, Application, Atom, Cardinality, Constant, Count, Function, Iff, Implies, Lambda,
    LambdaVar, Not, Number, Or, Quantifier, SlashedExists, SortedCardinality, SortedCount,
    SortedQuantifier, Variable, beta_reduce, free_variables, substitute,
)

# The two implementations of first-order substitution of a variable: the generic one the
# tableau checker and the beta-reducer call, and the one the proof searches call.
SUBSTITUTIONS = [pytest.param(substitute, id="generic"), pytest.param(_subst_var, id="search")]

x, x0, x1, x2, y = (Variable(n) for n in ("x", "x0", "x1", "x2", "y"))
POOL = ("x", "x0", "x1", "y")


def P(t):
    return Atom("P", (t,))


def R(s, t):
    return Atom("R", (s, t))


# --------------------------------------------------------------------------- #
# The oracle: a Tarski evaluator over a finite structure.
# --------------------------------------------------------------------------- #

class Structure(types.SimpleNamespace):
    """domain, constants, f (unary function table), P, R (relations), sorts."""


def _term(t, st, g):
    if isinstance(t, Variable):
        return g[t.name]
    if isinstance(t, Constant):
        return st.constants[t.name]
    if isinstance(t, Function):
        return st.f[tuple(_term(a, st, g) for a in t.args)]
    if isinstance(t, Number):
        return t.value
    if isinstance(t, Cardinality):
        return sum(1 for d in st.domain if _holds(t.formula, st, {**g, t.variable.name: d}))
    if isinstance(t, SortedCardinality):
        return sum(1 for d in st.sorts[t.sort]
                   if _holds(t.formula, st, {**g, t.variable.name: d}))
    raise AssertionError(f"term not covered: {t!r}")


def _count_test(op, bound, found):
    return {"ge": found >= bound, "le": found <= bound, "eq": found == bound}[op]


def _holds(f, st, g):
    if isinstance(f, Atom):
        args = tuple(_term(a, st, g) for a in f.args)
        if f.predicate == "=":
            return args[0] == args[1]
        if f.predicate == "≠":
            return args[0] != args[1]
        return args in (st.P if f.predicate == "P" else st.R)
    if isinstance(f, Not):
        return not _holds(f.formula, st, g)
    if isinstance(f, And):
        return _holds(f.left, st, g) and _holds(f.right, st, g)
    if isinstance(f, Or):
        return _holds(f.left, st, g) or _holds(f.right, st, g)
    if isinstance(f, Implies):
        return (not _holds(f.left, st, g)) or _holds(f.right, st, g)
    if isinstance(f, Iff):
        return _holds(f.left, st, g) == _holds(f.right, st, g)
    if isinstance(f, (Quantifier, SortedQuantifier)):
        universe = st.domain if isinstance(f, Quantifier) else st.sorts[f.sort]
        values = (_holds(f.formula, st, {**g, f.variable.name: d}) for d in universe)
        return all(values) if f.type == "∀" else any(values)
    if isinstance(f, (Count, SortedCount)):
        universe = st.domain if isinstance(f, Count) else st.sorts[f.sort]
        found = sum(1 for d in universe if _holds(f.formula, st, {**g, f.variable.name: d}))
        return _count_test(f.op, f.n.value, found)
    raise AssertionError(f"formula not covered: {f!r}")


def _random_structure(rng):
    size = rng.choice((1, 2, 3))
    domain = tuple(range(size))
    pairs = list(itertools.product(domain, domain))
    return Structure(
        domain=domain,
        constants={"ca": rng.choice(domain), "cb": rng.choice(domain)},
        f={(d,): rng.choice(domain) for d in domain},
        P={(d,) for d in domain if rng.random() < 0.5},
        R={p for p in pairs if rng.random() < 0.5},
        sorts={"S": tuple(d for d in domain if rng.random() < 0.6) or (rng.choice(domain),)},
    )


def _names(*nodes):
    out = set()
    for node in nodes:
        out |= {v.name for v in free_variables(node) if isinstance(v, Variable)}
    return out


def _assignments(names, domain):
    names = sorted(names)
    for values in itertools.product(domain, repeat=len(names)):
        yield dict(zip(names, values))


def _lemma_violation(phi, var, term, result, structures):
    """The first (structure, assignment) where the value lemma fails, or None."""
    names = _names(phi, term, result) | {var.name}
    for st in structures:
        for g in _assignments(names, st.domain):
            expected = _holds(phi, st, {**g, var.name: _term(term, st, g)})
            if _holds(result, st, g) != expected:
                return st, g
    return None


def _free_variable_violation(phi, var, term, result):
    expected = _names(phi) - {var.name}
    if var.name in _names(phi):
        expected |= _names(term)
    got = _names(result)
    return None if got == expected else (sorted(got), sorted(expected))


# --------------------------------------------------------------------------- #
# Hand-derived cases, one per binder family and per implementation.
# --------------------------------------------------------------------------- #

class Family:
    """One binder shape: how to build it around a body."""

    def __init__(self, name, bind, semantic=True):
        self.name, self.bind, self.semantic = name, bind, semantic

    def __repr__(self):
        return self.name


FAMILIES = [
    Family("forall", lambda v, b: Quantifier("∀", v, b)),
    Family("exists", lambda v, b: Quantifier("∃", v, b)),
    Family("sorted_forall", lambda v, b: SortedQuantifier("∀", v, "S", b)),
    Family("sorted_exists", lambda v, b: SortedQuantifier("∃", v, "S", b)),
    Family("count_ge", lambda v, b: Count("ge", Number(2), v, b)),
    Family("count_eq", lambda v, b: Count("eq", Number(1), v, b)),
    Family("sorted_count", lambda v, b: SortedCount("le", Number(1), v, "S", b)),
    # a cardinality is a TERM, so it sits in a comparison
    Family("cardinality", lambda v, b: Atom("=", (Cardinality(v, b), Number(1)))),
    Family("sorted_cardinality",
           lambda v, b: Atom("=", (SortedCardinality(v, "S", b), Number(1)))),
    Family("slashed", lambda v, b: SlashedExists(v, ("z",), b), semantic=False),
]


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
@pytest.mark.parametrize("fam", FAMILIES, ids=repr)
class TestBinderNamedLikeTheReplacement:
    def test_the_target_does_not_occur_and_the_new_binder_must_not_be_spelled_like_it(
            self, fam, subst):
        # φ = B x1. P(x1), target x0, replacement x1.
        #   x0 does not occur in φ, so φ[x0 := x1] is φ itself up to the name of the bound
        #   variable, and x1 must stay out of the free variables: the binder x1 would capture
        #   the incoming x1, so it is renamed; every candidate of the shape x<digits> that is
        #   taken is {x0 (target), x1 (replacement, old binder, body)}; the first free one
        #   is x2. φ[x0 := x1] = B x2. P(x2).
        phi = fam.bind(x1, P(x1))
        got = subst(phi, x0, x1)
        assert got == fam.bind(x2, P(x2))
        assert _names(got) == set() or fam.name == "slashed"

    def test_the_target_occurs_beside_the_binder(self, fam, subst):
        # φ = B x1. R(x0, x1), target x0, replacement x1: x0 occurs, so it is in the body's
        # names; x2 is the first free name. φ[x0 := x1] = B x2. R(x1, x2); x1 is free.
        phi = fam.bind(x1, R(x0, x1))
        got = subst(phi, x0, x1)
        assert got == fam.bind(x2, R(x1, x2))
        assert "x1" in _names(got)

    def test_the_binder_is_the_replacement_and_the_candidate_is_the_target(self, fam, subst):
        # φ = B y. P(y), target y0, replacement y. y0 does not occur in φ. The binder y would
        # capture the incoming y; the candidate is y0, which is the TARGET: the first free
        # name must skip it. avoid = {y, y0}: result B y1. P(y1), no free variable.
        y0, y1 = Variable("y0"), Variable("y1")
        phi = fam.bind(y, P(y))
        got = subst(phi, y0, y)
        assert got == fam.bind(y1, P(y1))


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
@pytest.mark.parametrize("fam", [f for f in FAMILIES if f.semantic], ids=repr)
def test_the_value_lemma_holds_for_the_defect_shape_in_every_small_structure(fam, subst):
    # B x1. P(x1) with x0 := x1 has no free variable, so its value does not depend on x1. The
    # defective result (the binder spelled x0, the matrix P(x1)) is P(x1) under every
    # assignment: it is false at x1 ↦ d whenever d is not in P, whatever B x1. P(x1) says.
    # Checked in every structure of at most three elements (see _every_structure).
    phi = fam.bind(x1, P(x1))
    got = subst(phi, x0, x1)
    assert _lemma_violation(phi, x0, x1, got, _every_structure(3)) is None, got.to_unicode_str()


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
def test_the_defective_result_is_a_different_formula(subst):
    # Guard on the oracle: ∀x0 P(x1) (what the defect returned) is not ∀x1 P(x1) in a
    # structure with P = {0}, domain {0, 1} and x1 ↦ 0: the first is P(0), true; the second is
    # false because P(1) fails.
    st = Structure(domain=(0, 1), constants={}, f={}, P={(0,)}, R=set(), sorts={"S": (0, 1)})
    defective = Quantifier("∀", x0, P(x1))
    right = Quantifier("∀", x1, P(x1))
    assert _holds(defective, st, {"x1": 0}) is True
    assert _holds(right, st, {"x1": 0}) is False
    assert _holds(subst(right, x0, x1), st, {"x1": 0}) is False


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
def test_nothing_is_renamed_when_nothing_is_captured(subst):
    # x := w does not meet the binder x1, so the formula keeps its binder.
    w = Variable("w")
    assert subst(Quantifier("∀", x1, R(x0, x1)), x0, w) == Quantifier("∀", x1, R(w, x1))


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
def test_a_binder_that_rebinds_the_target_stops_the_substitution(subst):
    phi = Quantifier("∃", x0, R(x0, x1))
    assert subst(phi, x0, x1) == phi


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
def test_the_new_binder_is_fresh_against_a_constant_spelled_like_it(subst):
    # φ = ∀x1 R(x1, x2) with x2 a CONSTANT (a description-logic image names individuals
    # like that), target x0, replacement x1. The candidate x0 is the target and x1 the
    # binder, so the first free name is x2 -- which is a constant of the matrix: renaming
    # onto it prints ∀x2 R(x2, x2), two different symbols spelled alike. avoid holds the
    # constant's name too, so the binder becomes x3.
    phi = Quantifier("∀", x1, R(x1, Constant("x2")))
    got = subst(phi, x0, x1)
    assert got == Quantifier("∀", Variable("x3"), R(Variable("x3"), Constant("x2")))


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
def test_the_new_binder_is_fresh_against_a_constant_of_the_replacement(subst):
    # φ = ∀x1 P(x1), target x0, replacement f(x1, x2) where x2 is a constant: the free
    # variable x1 is captured by the binder, and the new binder may not be spelled like the
    # replacement's constant x2 either: the candidates x0 (target), x1 (binder) and x2
    # (constant) are taken, so x3.
    replacement = Function("g", (x1, Constant("x2")))
    phi = Quantifier("∀", x1, P(x1))
    got = subst(phi, x0, replacement)
    assert got == Quantifier("∀", Variable("x3"), P(Variable("x3")))


# --------------------------------------------------------------------------- #
# A caller: the typed writer lowers a counting quantifier by substituting witnesses.
# --------------------------------------------------------------------------- #

def test_the_typed_writers_lowering_of_nested_counts_keeps_their_meaning():
    # A = ∃≥1 x0:S ∃≤1 x0:S (P(x0) ∧ x0 = x0). The inner count is a sentence ("at most one
    # S-element has P") that does not depend on the outer x0, and S is not empty, so A holds
    # exactly when at most one S-element has P. Lowering the inner count first gives binders
    # x0_0 and x0_1; the outer lowering substitutes its own witnesses x0_0, x0_1 for x0 in a
    # matrix that already binds x0_0 and x0_1, so those binders are renamed, and a new binder
    # spelled x0 (the substituted variable) turned the matrix into one that depends on the
    # outer witness: with P = {1, 2} on S = {0, 1, 2} the lowering held (witness 0 is no P),
    # while A is false (two elements have P).
    from unicode_fol_kit.atp.tptp_tff import _expand_all_sorted_counts
    v = Variable("x0")
    leaf = And(P(v), Atom("=", (v, v)))
    nested = SortedCount("ge", Number(1), v, "S", SortedCount("le", Number(1), v, "S", leaf))
    lowered = _expand_all_sorted_counts(nested)
    for st in _every_structure(3):
        at_most_one = len([d for d in st.sorts["S"] if (d,) in st.P]) <= 1
        assert _holds(nested, st, {}) == at_most_one
        assert _holds(lowered, st, {}) == at_most_one, (st.P, st.sorts)


# --------------------------------------------------------------------------- #
# The lambda binder.
# --------------------------------------------------------------------------- #

def _lam(param, body):
    return Lambda(LambdaVar(param), body)


def test_a_lambda_parameter_renamed_away_from_the_replacement_is_not_spelled_like_the_target():
    # (λx. x)[x0 := x] with the LambdaVars x0 and x: x0 does not occur free, so the term is
    # unchanged up to the parameter's name -- an identity function whose body is its own
    # parameter. The parameter x is the replacement's variable, so it is renamed; the first
    # candidate x0 is the target, so it is x1: λx1. x1. No free variable.
    got = substitute(_lam("x", LambdaVar("x")), LambdaVar("x0"), LambdaVar("x"))
    assert got == _lam("x1", LambdaVar("x1"))
    assert free_variables(got) == set()


def test_a_closed_lambda_term_reduces_to_the_atom_of_its_inner_binder():
    # ((λx. (λx0. λx. Q(x)) x) a) b, closed. The inner redex has the outer parameter x as its
    # argument; x0 is not used, so it is λx. Q(x) with the INNER x (the λx inside never sees
    # the outer one). Then (λx. λy. Q(y)) a b = (λy. Q(y)) b = Q(b). Capturing gave λx0. Q(x)
    # with the OUTER x: ... a b = Q(a).
    x, x0, a, b = LambdaVar("x"), LambdaVar("x0"), Constant("alpha"), Constant("beta")
    inner = Application(_lam("x0", _lam("x", Atom("Q", (x,)))), x)
    term = Application(Application(Lambda(x, inner), a), b)
    assert beta_reduce(term) == Atom("Q", (b,))
    assert eliminate_lambdas(term) == Atom("Q", (b,))


def test_beta_reduction_does_not_capture_through_a_parameter_spelled_like_the_argument():
    # (λx0. λx. x) x  →  λ·. ·  the identity: x0 is not used, the inner λx binds its own x.
    term = Application(_lam("x0", _lam("x", LambdaVar("x"))), LambdaVar("x"))
    got = beta_reduce(term)
    assert isinstance(got, Lambda) and got.body == got.param
    assert free_variables(got) == set()


# --------------------------------------------------------------------------- #
# The slashed existential: the slash set names a variable that must stay out of reach.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("subst", SUBSTITUTIONS)
def test_a_slashed_binder_avoids_the_target_and_its_own_slash_names(subst):
    # φ = ∃x1/{x2} P(x1), target x0, replacement x1. x1 captures the incoming x1, so it is
    # renamed; taken: the target x0, the binder x1, the slash name x2. The first free name
    # is x3, and the slash set is untouched.
    phi = SlashedExists(x1, ("x2",), P(x1))
    got = subst(phi, x0, x1)
    assert got == SlashedExists(Variable("x3"), ("x2",), P(Variable("x3")))


# --------------------------------------------------------------------------- #
# The brute-force check on random formulas.
# --------------------------------------------------------------------------- #

def _random_term(rng, depth=1, small=False):
    """A variable of the pool, a constant, or (unless ``small``) ``f`` of a term."""
    r = rng.random()
    if r < 0.62 or depth == 0:
        return Variable(rng.choice(POOL))
    if r < 0.8 or small:
        return Constant(rng.choice(("ca", "cb")))
    return Function("f", (_random_term(rng, depth - 1),))


def _random_formula(rng, depth, small=False):
    """A random formula over ``P``, ``R``, ``=`` (``small``: ``P`` and ``=`` only)."""
    r = rng.random()
    if depth == 0 or r < 0.22:
        k = rng.random()
        if k < (0.6 if small else 0.4):
            return P(_random_term(rng, small=small))
        if k < 0.8 and not small:
            return R(_random_term(rng), _random_term(rng))
        return Atom("=", (_random_term(rng, small=small), _random_term(rng, small=small)))
    if r < 0.45:
        if rng.random() < 0.25:
            return Not(_random_formula(rng, depth - 1, small))
        connective = rng.choice((And, Or, Implies, Iff))
        return connective(_random_formula(rng, depth - 1, small),
                          _random_formula(rng, depth - 1, small))
    v = Variable(rng.choice(POOL))
    body = _random_formula(rng, depth - 1, small)
    k = rng.randrange(8)
    if k in (0, 1, 7):
        return Quantifier(rng.choice("∀∃"), v, body)
    if k == 2:
        return SortedQuantifier(rng.choice("∀∃"), v, "S", body)
    if k == 3:
        return Count(rng.choice(("ge", "le", "eq")), Number(rng.randrange(3)), v, body)
    if k == 4:
        return SortedCount(rng.choice(("ge", "le", "eq")), Number(rng.randrange(3)), v, "S", body)
    if k == 5:
        return Atom("=", (Cardinality(v, body), Number(rng.randrange(3))))
    return Atom("=", (SortedCardinality(v, "S", body), Number(rng.randrange(3))))


def _every_structure(max_size):
    """EVERY structure with at most ``max_size`` elements over ``P``, ``ca``, ``cb`` and ``S``.

    ``P`` is any subset, the constants any elements, ``S`` any non-empty subset: the signature
    of the formulas generated with ``small=True``.
    """
    for size in range(1, max_size + 1):
        domain = tuple(range(size))
        subsets = [tuple(d for d, b in zip(domain, bits) if b)
                   for bits in itertools.product((False, True), repeat=size)]
        for p in subsets:
            for ca, cb in itertools.product(domain, repeat=2):
                for sort in subsets:
                    if sort:
                        yield Structure(domain=domain, constants={"ca": ca, "cb": cb}, f={},
                                        P={(d,) for d in p}, R=set(), sorts={"S": sort})


def _battery(seed, formulas, structures_per_formula, depth, exhaustive=False):
    """Run the two lemmas on ``formulas`` random cases; return the violations found.

    With ``exhaustive`` the formulas use ``P`` and ``=`` only and every case is checked in
    EVERY structure of at most three elements over that signature (``structures_per_formula``
    is then ignored); otherwise in that many random structures.
    """
    rng = random.Random(seed)
    every = list(_every_structure(3)) if exhaustive else None
    found = []
    for _ in range(formulas):
        phi = _random_formula(rng, depth, small=exhaustive)
        var = Variable(rng.choice(POOL))
        term = _random_term(rng, small=exhaustive)
        structures = every if exhaustive else [
            _random_structure(rng) for _ in range(structures_per_formula)]
        for subst in (substitute, _subst_var):
            result = subst(phi, var, term)
            bad = _free_variable_violation(phi, var, term, result)
            if bad is not None:
                found.append(("free variables", subst.__name__, phi, var, term, bad))
                continue
            bad = _lemma_violation(phi, var, term, result, structures)
            if bad is not None:
                found.append(("value", subst.__name__, phi, var, term, bad))
    return found


def _describe(violations):
    return [(kind, impl, phi.to_unicode_str(), var.name, term.to_unicode_str(), detail)
            for kind, impl, phi, var, term, detail in violations[:3]]


def test_the_two_lemmas_hold_on_random_formulas():
    violations = _battery(seed=20260401, formulas=260, structures_per_formula=5, depth=3)
    assert not violations, _describe(violations)


def test_the_value_lemma_holds_in_every_structure_of_at_most_three_elements():
    # 554 structures: 2 on one element, 48 on two, 504 on three; every assignment of the
    # variables of the case in each. Few formulas, because each is checked in all of them.
    assert len(list(_every_structure(3))) == 554
    violations = _battery(seed=3, formulas=14, structures_per_formula=0, depth=2,
                          exhaustive=True)
    assert not violations, _describe(violations)


def test_the_free_variable_lemma_holds_on_many_more_formulas():
    # No evaluator, so deeper and a lot more formulas.
    rng = random.Random(7)
    for _ in range(2500):
        phi = _random_formula(rng, 4)
        var = Variable(rng.choice(POOL))
        term = _random_term(rng)
        for subst in (substitute, _subst_var):
            result = subst(phi, var, term)
            assert _free_variable_violation(phi, var, term, result) is None, (
                subst.__name__, phi.to_unicode_str(), var.name, term.to_unicode_str(),
                result.to_unicode_str())


def test_the_generic_substitution_and_the_searchs_give_the_same_formula():
    # A checker that recomputes an instance with ``substitute`` compares it with the one a proof
    # search recorded with ``_subst_var``, formula for formula: the two must not only be
    # alpha-equivalent, they must spell the renamed binders alike.
    rng = random.Random(3)
    for _ in range(3000):
        phi = _random_formula(rng, rng.choice((2, 3, 4)))
        if rng.random() < 0.25:
            binder = rng.choice(POOL)
            slashed = (rng.choice([n for n in POOL if n != binder]),)
            phi = And(SlashedExists(Variable(binder), slashed, _random_formula(rng, 2)), phi)
        var = Variable(rng.choice(POOL))
        term = _random_term(rng)
        if rng.random() < 0.15:
            term = Function("g", (Variable(rng.choice(POOL)), Constant(rng.choice(("x2", "x0", "ca")))))
        assert substitute(phi, var, term) == _subst_var(phi, var, term), (
            phi.to_unicode_str(), var.name, term.to_unicode_str())


def test_the_free_variable_lemma_holds_for_a_slashed_binder_and_a_variable_replacement():
    # A slash entry is a free occurrence of the variable it names, and a variable replacement
    # renames the entry, so the lemma holds with the slash sets counted as free occurrences.
    rng = random.Random(11)
    for _ in range(600):
        body = _random_formula(rng, 2)
        binder = rng.choice(POOL)
        # a slash set never names its own binder (a variable cannot be independent of itself)
        others = [n for n in POOL if n != binder]
        slashed = tuple(sorted(set(rng.choice(others) for _ in range(rng.randrange(1, 3)))))
        phi = SlashedExists(Variable(binder), slashed, body)
        if rng.random() < 0.5:
            phi = And(phi, _random_formula(rng, 1))
        var = Variable(rng.choice(POOL))
        term = Variable(rng.choice(POOL + ("x2",)))
        for subst in (substitute, _subst_var):
            result = subst(phi, var, term)
            assert _free_variable_violation(phi, var, term, result) is None, (
                subst.__name__, phi.to_unicode_str(), var.name, term.to_unicode_str(),
                result.to_unicode_str())
