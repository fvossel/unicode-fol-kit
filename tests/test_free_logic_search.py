"""Tests for the bounded free-logic model search: free_find_model, free_countermodel,
free_is_valid, free_entails (semantics/free_logic.py).

Every expected verdict is hand-derived in a comment. The module implements NEGATIVE
free logic by default (see free_logic.py's module docstring): an atom with a
non-denoting term is simply false, and self-identity ``t=t`` is also false for a
non-denoting ``t`` (the "positive" policy makes only the LITERAL-same-term-twice
case of self-identity true instead). free_satisfies also implements the classic
inner/outer domain split independently of the denoting/non-denoting distinction: a
constant CAN denote an "outer" object that is not in the "existing" (inner) domain
quantifiers range over. Several tests below exploit that second mechanism, which is
available under EITHER policy (it does not depend on how non-denotation is handled),
so those verdicts are policy-independent, and the tests check both policies to make
that explicit.
"""

import random

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable, Constant,
)
from unicode_fol_kit.semantics.free_logic import (
    FreeModel, free_satisfies, free_holds,
    free_find_model, free_countermodel, free_is_valid, free_entails,
    MAX_FUNCTION_ARITY,
)
from unicode_fol_kit.semantics.modelfinder import is_valid_finite


x = Variable("x")
y = Variable("y")
c = Constant("c")
Px = lambda t: Atom("P", [t])
Qx = lambda t: Atom("Q", [t])
Ec = Atom("E!", [c])
ALL_P = Quantifier("∀", x, Px(x))
EXISTS_P = Quantifier("∃", x, Px(x))


# --------------------------------------------------------------------------- #
# Classical existential generalisation (EG) and universal instantiation (UI)
# failures — the defining phenomena of free logic.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("policy", ["negative", "positive"])
def test_universal_instantiation_fails(policy):
    # UI ∀x P(x) |- P(c) is NOT valid in free logic: c may denote an object outside
    # the inner (existing) domain, so P(c) can fail even though every EXISTING thing
    # is P. This uses the inner/outer split, not raw non-denotation, so it holds
    # under BOTH policies (verified by parametrizing).
    assert free_entails([ALL_P], Px(c), policy=policy) is False
    assert free_is_valid(Implies(ALL_P, Px(c)), policy=policy) is False

    # The witnessing countermodel must be a genuine countermodel: verify directly
    # with free_satisfies (the same discipline free_countermodel applies internally
    # before returning — rel_valid / cf_valid's "verified countermodel" contract).
    cm = free_countermodel(Implies(ALL_P, Px(c)), policy=policy)
    assert cm is not None
    assert free_satisfies(ALL_P, cm, {}, policy) is True
    assert free_satisfies(Px(c), cm, {}, policy) is False


@pytest.mark.parametrize("policy", ["negative", "positive"])
def test_guarded_universal_instantiation_is_valid(policy):
    # Guarded UI (∀x P(x) ∧ E!(c)) -> P(c) IS a free-logic theorem: E!(c) forces c's
    # denotation to be an EXISTING object, and ∀x P(x) says every existing object is
    # P, so P(c) follows. This is a genuine semantic validity (not just "no
    # countermodel found"), so the bounded search should report it valid at any
    # reasonable max_size.
    guarded = Implies(And(ALL_P, Ec), Px(c))
    assert free_is_valid(guarded, policy=policy) is True
    assert free_entails([ALL_P, Ec], Px(c), policy=policy) is True


@pytest.mark.parametrize("policy", ["negative", "positive"])
def test_existential_generalization_fails(policy):
    # EG P(c) |- exists x P(x) is NOT valid. Under a naive "gappy term" free logic
    # with no outer domain, a NEGATIVE policy alone would make this valid (P(c) is
    # false whenever c doesn't denote, so the entailment holds vacuously whenever the
    # antecedent could fail). But free_logic.py's FreeModel has a genuine inner/outer
    # split: c can denote a "merely possible" OUTER object that satisfies P yet is
    # NOT in the inner "existing" domain that ∃ ranges over. That witness makes P(c)
    # true and "exists x P(x)" false, refuting EG regardless of policy (the atom is
    # not non-denoting in that witness, so the negative/positive distinction never
    # even applies here) -- verified below by parametrizing over both policies.
    assert free_entails([Px(c)], EXISTS_P, policy=policy) is False
    cm = free_countermodel(Implies(Px(c), EXISTS_P), policy=policy)
    assert cm is not None
    assert free_satisfies(Px(c), cm, {}, policy) is True
    assert free_satisfies(EXISTS_P, cm, {}, policy) is False
    # The witness need not even use non-denotation: c denotes in every candidate
    # model considered here (constants.get('c') is set whenever the search finds
    # this particular refutation route), confirming the inner/outer split is doing
    # the work, not the non-denoting-atom policy.


@pytest.mark.parametrize("policy", ["negative", "positive"])
def test_guarded_existential_generalization_is_valid(policy):
    # Guarded EG (P(c) ∧ E!(c)) |- exists x P(x): if c exists (E!(c)) and P(c), then
    # c's denotation is both an existing object and P, so it is itself the witness
    # for "exists x P(x)". Genuinely valid, both policies.
    assert free_entails([Px(c), Ec], EXISTS_P, policy=policy) is True


# --------------------------------------------------------------------------- #
# Classical tautologies remain valid: the evaluator is two-valued (an atom with a
# non-denoting term is simply False, never a third "gap" value), so excluded middle
# survives free logic untouched.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("policy", ["negative", "positive"])
def test_excluded_middle_is_valid(policy):
    assert free_is_valid(Or(Px(c), Not(Px(c))), policy=policy) is True
    # A tautology has NO countermodel at any size -- confirm directly too.
    assert free_countermodel(Or(Px(c), Not(Px(c))), policy=policy) is None


# --------------------------------------------------------------------------- #
# Denotation facts: E!(c) <-> exists x (x = c). Both directions are valid: E!(c)
# means c denotes an object in `existing`, which is exactly what witnesses the
# existential (with x := that object); conversely if some existing x equals c's
# denotation, c must denote that (existing) object, so E!(c) holds. The equality
# case with a genuinely shared denotation never touches the non-denoting branch
# of _atom, so this holds under both policies too.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("policy", ["negative", "positive"])
def test_denotation_iff_existential_self_identity(policy):
    exists_eq_c = Quantifier("∃", x, Atom("=", [x, c]))
    assert free_is_valid(Implies(Ec, exists_eq_c), policy=policy) is True
    assert free_is_valid(Implies(exists_eq_c, Ec), policy=policy) is True


# --------------------------------------------------------------------------- #
# Positive vs negative policy: they can ONLY differ on an atom with a non-denoting
# term, and self-identity t=t (SAME term syntactically on both sides) is the
# textbook case: positive free logic stipulates t=t true even when t is
# non-denoting; negative free logic does not.
# --------------------------------------------------------------------------- #

def test_self_identity_policy_divergence_at_search_level():
    cc = Atom("=", [c, c])
    # Positive: c=c holds even in the (legitimate, searched) candidate model where c
    # is entirely non-denoting -- so it is valid at EVERY candidate model, hence
    # free_is_valid reports True and free_countermodel finds nothing.
    assert free_is_valid(cc, policy="positive") is True
    assert free_countermodel(cc, policy="positive") is None

    # Negative: the search DOES try a model where c is omitted from `constants`
    # (non-denoting); there c=c is false under the negative policy, which is a
    # genuine countermodel to c=c's validity.
    assert free_is_valid(cc, policy="negative") is False
    cm = free_countermodel(cc, policy="negative")
    assert cm is not None
    assert "c" not in cm.constants                       # c is non-denoting there
    assert free_satisfies(cc, cm, {}, "negative") is False


# --------------------------------------------------------------------------- #
# The empty existing domain: free logic (unlike classical FOL) allows the inner
# domain to be empty, so "not exists x P(x)" is trivially satisfiable by an empty
# `existing`, regardless of the predicate's extension over the (nonempty) outer
# domain. Classical FOL requires a nonempty domain, so this model has NO classical
# counterpart.
# --------------------------------------------------------------------------- #

def test_empty_existing_domain_is_a_legitimate_model():
    m = free_find_model(Not(EXISTS_P))
    assert m is not None
    assert m.existing == frozenset()          # the witnessing existing domain is empty
    assert free_satisfies(Not(EXISTS_P), m, {}, "negative") is True


# --------------------------------------------------------------------------- #
# free_find_model / free_countermodel return None (not a spurious model / witness)
# for the boundary boolean case, and free_is_valid / free_entails delegate to them.
# --------------------------------------------------------------------------- #

def test_valid_formula_has_no_countermodel():
    guarded = Implies(And(ALL_P, Ec), Px(c))
    assert free_countermodel(guarded) is None
    assert free_find_model(Not(guarded)) is None


def test_satisfiable_but_not_valid_formula_has_both():
    # P(c) is satisfiable (some model makes it true) but not valid (some model makes
    # it false, e.g. c non-denoting) -- both searches should succeed.
    assert free_find_model(Px(c)) is not None
    assert free_countermodel(Px(c)) is not None


# --------------------------------------------------------------------------- #
# Input validation: unknown policy / domain_split are rejected up front, and a
# function above MAX_FUNCTION_ARITY is rejected with a clear message rather than
# silently starving max_candidates at every domain size (see free_logic._search's
# docstring: an entirely-skipped search would otherwise misleadingly look like a
# completed bounded search that just found nothing).
# --------------------------------------------------------------------------- #

def test_unknown_policy_rejected():
    with pytest.raises(ValueError, match="policy"):
        free_is_valid(Px(c), policy="bogus")


def test_unknown_domain_split_rejected():
    with pytest.raises(ValueError, match="domain_split"):
        free_is_valid(Px(c), domain_split="bogus")


def test_high_arity_function_rejected_cleanly():
    from unicode_fol_kit.fol.nodes import Function
    assert MAX_FUNCTION_ARITY == 2                    # documents the current bound
    f3 = Function("f", [x, y, Variable("z")])          # arity 3 > MAX_FUNCTION_ARITY
    with pytest.raises(ValueError, match="MAX_FUNCTION_ARITY"):
        free_find_model(Atom("P", [f3]), max_size=1)


def test_exhausted_candidate_budget_raises_instead_of_silently_returning_none():
    # max_candidates=1 makes every domain size infeasible for this tiny signature (1
    # constant + 1 unary predicate already needs 8 candidates at size 1 -- see
    # _candidate_count), so NOTHING is actually searched; a bare None here would look
    # like a completed (if narrow) bounded search rather than an aborted one.
    with pytest.raises(ValueError, match="max_candidates"):
        free_find_model(Px(c), max_size=1, max_candidates=1)


# --------------------------------------------------------------------------- #
# Differential sanity: on formulas WITHOUT constants/functions, and with the
# existing/outer split forced to "total" (everything in the outer domain exists --
# the classical-FOL-equivalent reading), free_is_valid must agree with the
# classical bounded is_valid_finite from semantics/modelfinder.py. Under
# domain_split="total" every atom's arguments are bound variables (always
# denoting), so _atom degenerates to exactly the classical Tarskian atom check, and
# quantifiers range over the full domain exactly like classical ones -- the two
# searches enumerate the identical interpretation space.
# --------------------------------------------------------------------------- #

_PREDS = ["P", "Q", "R"]
_VARS = [Variable("x"), Variable("y")]


def _random_atom(rng: random.Random) -> Atom:
    pred = rng.choice(_PREDS)
    arity = rng.choice([1, 1, 2])
    return Atom(pred, [rng.choice(_VARS) for _ in range(arity)])


def _random_formula(rng: random.Random, depth: int):
    if depth <= 0 or rng.random() < 0.35:
        return _random_atom(rng)
    choice = rng.random()
    if choice < 0.15:
        return Not(_random_formula(rng, depth - 1))
    if choice < 0.30:
        return And(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    if choice < 0.45:
        return Or(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    if choice < 0.55:
        return Xor(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    if choice < 0.70:
        return Implies(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    if choice < 0.80:
        return Iff(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    var = rng.choice(_VARS)
    qtype = rng.choice(["∀", "∃"])
    return Quantifier(qtype, var, _random_formula(rng, depth - 1))


def test_agrees_with_classical_modelfinder_when_everything_exists():
    # Fixed seed: reproducible, hand-inspectable if it ever fails.
    rng = random.Random(20260721)
    checked = 0
    for _ in range(30):
        formula = _random_formula(rng, depth=3)
        expected = is_valid_finite(formula, max_size=3)
        actual = free_is_valid(formula, max_size=3, domain_split="total")
        assert actual == expected, (
            f"classical/free (total-domain) mismatch on {formula.to_prover9()!r}: "
            f"classical={expected} free={actual}"
        )
        checked += 1
    assert checked == 30
