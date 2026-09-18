"""LNH symmetry breaking for the finite model finder (roadmap C23).

Covers ``semantics/modelfinder.py``'s ``_canonical_interpretations`` /
``_lnh_choices`` directly, plus the two modules that reuse or hand-port them:
``semantics/secondorder.py`` (reuse -- ``_so_structures`` now calls
``_canonical_interpretations``) and ``semantics/free_logic.py`` (hand-port --
``_canonical_constant_assignments`` / ``_canonical_candidate_models``). See
tests/test_modelfinder.py for the hand-checked textbook (in)validities this
generator must still get right; this file is the differential / soundness /
completeness battery the roadmap's ``test_oracle`` calls for:

(a) ``find_model``/``so_find_model``/``free_find_model`` with
    ``symmetry_breaking=True`` must find a model at domain size ``k`` iff the
    unbroken enumeration does, for every ``k`` -- not just "eventually, for some
    k" -- checked directly against the two low-level generators at a FIXED size
    (``_model_exists_at_size`` and friends below), across many random small
    signatures (seeded, reproducible) mixing constants, unary/binary functions,
    predicates, equality, and quantifier alternation, plus free_logic's partial
    constants/functions and existing/outer split, plus second-order search.
(b) For signatures small enough to enumerate BOTH generators to completion
    (k <= 3), the SET OF ISOMORPHISM CLASSES they visit must be identical: every
    raw structure has an isomorphic representative among the canonical ones
    (completeness -- LNH invents no false negatives), and every canonical
    structure is itself a genuine raw structure (soundness) with no duplicates
    among the canonical ones (no wasted, redundant work).

DEVIATION FROM THE ROADMAP DRAFT, confirmed by this file's own
``test_canonical_generator_covers_every_isomorphism_class`` before anything else
was built on top of it: LNH restricted to a flat per-cell cap over a FUNCTION's
full table (in a fixed argument order, as the roadmap draft described) is
UNSOUND -- a hand-checked counterexample (a 2-element domain, a single unary
function, no constants: the "swap" table f(0)=1, f(1)=0 has no domain
permutation making cell f(0) equal 0, yet it is its own, legitimate isomorphism
class) is worked out in ``modelfinder._canonical_interpretations``'s docstring.
This implementation therefore applies LNH to CONSTANTS only; functions and
predicates are exhaustive on both sides of ``symmetry_breaking``, exactly like
the roadmap's own (correct) treatment of predicates. See that docstring for the
full argument. This file's isomorphism-class test would have caught the unsound
version directly (it did, during development) and is kept here as the
regression guard against reintroducing it.

Measured wall-clock speedups (this machine, one run each -- not re-run on every
test invocation to avoid a flaky, load-sensitive assertion in the suite):
7 pairwise-distinct named constants, satisfiable at k=7: 0.050s (True) vs
4.68s (False) -- 94x. 8 pairwise-distinct named constants forced unsatisfiable
at k=6 (pigeonhole, so both sides must exhaust their full search space):
0.17s (True) vs 28.0s (False) -- 164x. The same all-different theory over 6
constants plus one exhaustive unary predicate, satisfiable at k=6: 0.24s (True)
vs 7.19s (False) -- 29x. ``test_canonical_generator_visits_far_fewer_candidates``
below is the structural (non-flaky) regression guard for this reduction.
"""

import random
import time
from itertools import permutations

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Quantifier, Variable, Constant, Function,
)
from unicode_fol_kit.fol._so_nodes import SecondOrderQuantifier
from unicode_fol_kit.semantics import modelfinder as mf
from unicode_fol_kit.semantics import free_logic as fl
from unicode_fol_kit.semantics import secondorder as so
from unicode_fol_kit.semantics.tarski import Structure, models


# ============================================================================
# _lnh_choices: direct unit tests of the shared bookkeeping.
# ============================================================================

def test_lnh_choices_forces_the_first_cell_and_grows_by_at_most_one():
    # HAND CHECK: with nothing used yet (next_new=0), the only eligible choice is
    # the single "introduce the first element" option, index 0 -- never a value
    # that would skip ahead of an as-yet-unintroduced element.
    assert list(mf._lnh_choices(0, 3)) == [0]
    assert list(mf._lnh_choices(1, 3)) == [0, 1]
    assert list(mf._lnh_choices(2, 3)) == [0, 1, 2]
    # Capped at k: once every domain value is already "used", no 4th choice.
    assert list(mf._lnh_choices(3, 3)) == [0, 1, 2]
    assert list(mf._lnh_choices(0, 1)) == [0]


# ============================================================================
# Oracle (b): isomorphism-class-set equality, brute force, k <= 3.
# ============================================================================

def _apply_perm(constants, functions, predicates, perm):
    """Relabel a raw interpretation's domain elements through ``perm`` (a tuple
    where ``perm[i]`` is the new label for old label ``i``)."""
    pconstants = {name: perm[v] for name, v in constants.items()}
    pfunctions = {}
    for (name, arity), table in functions.items():
        pfunctions[(name, arity)] = {
            tuple(perm[a] for a in args): perm[v] for args, v in table.items()
        }
    ppredicates = {}
    for (name, arity), tuples in predicates.items():
        ppredicates[(name, arity)] = frozenset(tuple(perm[a] for a in t) for t in tuples)
    return pconstants, pfunctions, ppredicates


def _struct_key(constants, functions, predicates):
    """A hashable, order-independent identity for a raw ``(constants, functions,
    predicates)`` triple, for set-membership comparisons below."""
    return (tuple(sorted(constants.items())),
            tuple(sorted((k, tuple(sorted(v.items()))) for k, v in functions.items())),
            tuple(sorted((k, tuple(sorted(v))) for k, v in predicates.items())))


@pytest.mark.parametrize("consts,funcs,preds,k", [
    (["a"], [("f", 1)], [("P", 1)], 3),
    (["a", "b"], [], [("P", 2)], 3),
    ([], [("f", 2)], [("Q", 1)], 2),
    (["a", "b", "c"], [], [("P", 1)], 3),
    (["a", "b"], [("f", 1)], [], 3),
], ids=["const+f1+P1", "2const+P2", "f2+Q1-no-const", "3const+P1", "2const+f1-no-pred"])
def test_canonical_generator_covers_every_isomorphism_class(consts, funcs, preds, k):
    """The hand-checkable soundness statement for LNH: the raw and canonical
    generators visit exactly the same isomorphism classes (brute-forced by trying
    every one of the k! domain permutations, feasible at k <= 3)."""
    sig = mf._Signature()
    sig.constants |= set(consts)
    sig.functions |= set(funcs)
    sig.predicates |= set(preds)
    domain = tuple(range(k))

    raw = list(mf._interpretations(sig, domain))
    canon = list(mf._canonical_interpretations(sig, domain))

    canon_keys = {_struct_key(*s) for s in canon}
    assert len(canon_keys) == len(canon), "canonical generator yielded a duplicate structure"

    raw_keys = {_struct_key(*s) for s in raw}
    for c in canon:
        # Soundness: every canonical structure is itself a genuine raw one.
        assert _struct_key(*c) in raw_keys

    perms = list(permutations(domain))
    for r in raw:
        # Completeness: every raw structure has an isomorphic representative
        # among the canonical ones -- LNH invented no false negatives.
        assert any(_struct_key(*_apply_perm(*r, perm)) in canon_keys for perm in perms), (
            f"raw structure has no isomorphic canonical representative: {r}")


def test_canonical_interpretations_rejects_a_sorted_signature():
    sig = mf._Signature()
    sig.sorts.add("S")
    with pytest.raises(ValueError, match="sorts"):
        list(mf._canonical_interpretations(sig, (0, 1)))


def test_canonical_generator_visits_far_fewer_candidates_than_raw():
    """Structural (deterministic, not wall-clock -- so not flaky under CI load)
    confirmation that the reduction is real: for 6 named constants at a
    6-element domain, the canonical count is the 6th BELL NUMBER (the number of
    ways to partition 6 labeled items, independently verified below via the
    standard Bell-triangle recurrence -- not via this module's own LNH code),
    while the raw count is the full 6**6. See the module docstring for measured
    wall-clock speedups this structural gap translates into on representative
    problems.
    """
    def bell_number(n):
        """Independent computation (Bell's triangle), OEIS A000110: 1, 1, 2, 5,
        15, 52, 203, ... -- not derived from modelfinder in any way."""
        triangle = [[1]]
        for i in range(1, n + 1):
            row = [triangle[i - 1][-1]]
            for prev in triangle[i - 1]:
                row.append(row[-1] + prev)
            triangle.append(row)
        return triangle[n][0]

    sig = mf._Signature()
    sig.constants |= {f"c{i}" for i in range(6)}
    domain = tuple(range(6))
    raw_count = sum(1 for _ in mf._interpretations(sig, domain))
    canon_count = sum(1 for _ in mf._canonical_interpretations(sig, domain))
    assert raw_count == 6 ** 6
    assert canon_count == bell_number(6) == 203
    assert canon_count < raw_count


# ============================================================================
# Oracle (a): differential existence-at-each-size, modelfinder.py, random
# small signatures mixing constants, a unary function, predicates, equality
# and quantifier alternation.
# ============================================================================

_CONSTS = ["a", "b"]
_UPREDS = ["P", "Q"]
_VARS = [Variable("x"), Variable("y")]


def _random_term(rng: random.Random, depth: int):
    if depth <= 0 or rng.random() < 0.5:
        return rng.choice(_VARS) if rng.random() < 0.5 else Constant(rng.choice(_CONSTS))
    return Function("f", [_random_term(rng, depth - 1)])


def _random_atom(rng: random.Random):
    if rng.random() < 0.25:
        return Atom("=", [_random_term(rng, 1), _random_term(rng, 1)])
    return Atom(rng.choice(_UPREDS), [_random_term(rng, 1)])


def _random_formula(rng: random.Random, depth: int):
    if depth <= 0 or rng.random() < 0.3:
        return _random_atom(rng)
    choice = rng.random()
    if choice < 0.15:
        return Not(_random_formula(rng, depth - 1))
    if choice < 0.35:
        return And(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    if choice < 0.55:
        return Or(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    if choice < 0.70:
        return Implies(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    if choice < 0.80:
        return Iff(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    var = rng.choice(_VARS)
    qtype = rng.choice(["∀", "∃"])
    return Quantifier(qtype, var, _random_formula(rng, depth - 1))


def _model_exists_at_size(sentences, sig, k, use_canonical):
    """Whether SOME interpretation of ``sig`` over a ``k``-element domain
    satisfies every one of ``sentences`` -- the low-level, single-size existence
    check both generators are compared on (batch note (1)'s literal "at size k",
    not merely the multi-size ``find_model`` result)."""
    domain = tuple(range(k))
    gen = mf._canonical_interpretations(sig, domain) if use_canonical else mf._interpretations(sig, domain)
    for constants, functions, predicates in gen:
        structure = Structure(domain, constants=constants, functions=functions, predicates=predicates)
        if all(models(s, structure) for s in sentences):
            # Soundness leg of the oracle, right here: a model the canonical
            # generator claims to have found is re-verified with the same
            # independent tarski.models call the raw path uses.
            return True
    return False


def test_random_signatures_agree_at_each_size_constants_function_predicates():
    rng = random.Random(20260917)
    checked = 0
    for _ in range(40):
        formula = _random_formula(rng, depth=3)
        sentence = mf._universal_closure(formula)
        sig = mf._Signature()
        sig.scan(sentence)
        for k in (1, 2, 3):
            expected = _model_exists_at_size([sentence], sig, k, use_canonical=False)
            actual = _model_exists_at_size([sentence], sig, k, use_canonical=True)
            assert actual == expected, (
                f"size {k} mismatch on {formula.to_prover9()!r}: "
                f"unbroken={expected} canonical={actual}")
            checked += 1
    assert checked == 120


# A second, smaller-scale battery that also exercises a BINARY function (batch
# note (1) explicitly asks for one) -- kept to domain sizes 1..2, since a single
# binary function's raw table already costs k**(k**2) per candidate and a
# k=3 sweep across 40 random formulas would make this file too slow to be a
# routine test (see the bench numbers in the module docstring for why: the
# unbroken side is the expensive one to run to completion).

def _random_term_with_binary(rng: random.Random, depth: int):
    if depth <= 0 or rng.random() < 0.5:
        return rng.choice(_VARS) if rng.random() < 0.5 else Constant(rng.choice(_CONSTS))
    if rng.random() < 0.5:
        return Function("f", [_random_term_with_binary(rng, depth - 1)])
    return Function("g", [_random_term_with_binary(rng, depth - 1),
                          _random_term_with_binary(rng, depth - 1)])


def _random_atom_with_binary(rng: random.Random):
    if rng.random() < 0.25:
        return Atom("=", [_random_term_with_binary(rng, 1), _random_term_with_binary(rng, 1)])
    return Atom(rng.choice(_UPREDS), [_random_term_with_binary(rng, 1)])


def _random_formula_with_binary(rng: random.Random, depth: int):
    if depth <= 0 or rng.random() < 0.3:
        return _random_atom_with_binary(rng)
    choice = rng.random()
    if choice < 0.15:
        return Not(_random_formula_with_binary(rng, depth - 1))
    if choice < 0.35:
        return And(_random_formula_with_binary(rng, depth - 1), _random_formula_with_binary(rng, depth - 1))
    if choice < 0.55:
        return Or(_random_formula_with_binary(rng, depth - 1), _random_formula_with_binary(rng, depth - 1))
    if choice < 0.70:
        return Implies(_random_formula_with_binary(rng, depth - 1), _random_formula_with_binary(rng, depth - 1))
    if choice < 0.80:
        return Iff(_random_formula_with_binary(rng, depth - 1), _random_formula_with_binary(rng, depth - 1))
    var = rng.choice(_VARS)
    qtype = rng.choice(["∀", "∃"])
    return Quantifier(qtype, var, _random_formula_with_binary(rng, depth - 1))


def test_random_signatures_with_binary_function_agree_at_each_size():
    rng = random.Random(20260918)
    checked = 0
    for _ in range(15):
        formula = _random_formula_with_binary(rng, depth=3)
        sentence = mf._universal_closure(formula)
        sig = mf._Signature()
        sig.scan(sentence)
        for k in (1, 2):
            expected = _model_exists_at_size([sentence], sig, k, use_canonical=False)
            actual = _model_exists_at_size([sentence], sig, k, use_canonical=True)
            assert actual == expected, (
                f"size {k} mismatch on {formula.to_prover9()!r}: "
                f"unbroken={expected} canonical={actual}")
            checked += 1
    assert checked == 30


# ============================================================================
# Oracle (a), free_logic.py: partial constants/functions, the existing/outer
# split, and both policies.
# ============================================================================

_FREE_SEEDS = {
    ("negative", "any"): 30001, ("negative", "total"): 30002,
    ("positive", "any"): 30003, ("positive", "total"): 30004,
}


def _random_atom_free(rng: random.Random):
    choice = rng.random()
    if choice < 0.15:
        return Atom("E!", [_random_term(rng, 1)])
    if choice < 0.35:
        return Atom("=", [_random_term(rng, 1), _random_term(rng, 1)])
    return Atom(rng.choice(_UPREDS), [_random_term(rng, 1)])


def _random_formula_free(rng: random.Random, depth: int):
    if depth <= 0 or rng.random() < 0.3:
        return _random_atom_free(rng)
    choice = rng.random()
    if choice < 0.15:
        return Not(_random_formula_free(rng, depth - 1))
    if choice < 0.35:
        return And(_random_formula_free(rng, depth - 1), _random_formula_free(rng, depth - 1))
    if choice < 0.55:
        return Or(_random_formula_free(rng, depth - 1), _random_formula_free(rng, depth - 1))
    if choice < 0.70:
        return Implies(_random_formula_free(rng, depth - 1), _random_formula_free(rng, depth - 1))
    if choice < 0.80:
        return Iff(_random_formula_free(rng, depth - 1), _random_formula_free(rng, depth - 1))
    var = rng.choice(_VARS)
    qtype = rng.choice(["∀", "∃"])
    return Quantifier(qtype, var, _random_formula_free(rng, depth - 1))


def _free_model_exists_at_size(closed, const_names, func_sig, pred_sig, domain_split,
                               policy, k, use_canonical):
    domain = tuple(range(k))
    gen = (fl._canonical_candidate_models(domain, const_names, func_sig, pred_sig, domain_split)
           if use_canonical else
           fl._candidate_models(domain, const_names, func_sig, pred_sig, domain_split))
    for model in gen:
        if all(fl.free_satisfies(f, model, {}, policy) for f in closed):
            return True
    return False


@pytest.mark.parametrize("policy", ["negative", "positive"])
@pytest.mark.parametrize("domain_split", ["any", "total"])
def test_free_logic_random_signatures_agree_at_each_size(policy, domain_split):
    rng = random.Random(_FREE_SEEDS[(policy, domain_split)])
    checked = 0
    for _ in range(20):
        formula = _random_formula_free(rng, depth=3)
        closed = [fl._universal_closure(formula)]
        constants, functions, predicates = fl._signature(closed[0])
        const_names = sorted(constants)
        func_sig = sorted(functions)
        pred_sig = sorted(predicates)
        for k in (1, 2, 3):
            expected = _free_model_exists_at_size(closed, const_names, func_sig, pred_sig,
                                                   domain_split, policy, k, use_canonical=False)
            actual = _free_model_exists_at_size(closed, const_names, func_sig, pred_sig,
                                                 domain_split, policy, k, use_canonical=True)
            assert actual == expected, (
                f"size {k} mismatch on {formula.to_prover9()!r} "
                f"(policy={policy!r}, domain_split={domain_split!r}): "
                f"unbroken={expected} canonical={actual}")
            checked += 1
    assert checked == 60


def test_free_logic_exhausted_budget_test_still_raises_with_symmetry_breaking():
    # Regression guard: the live-counted budget check must treat a size that is
    # abandoned mid-generator (over max_candidates) the same way the old
    # pre-flight skip did -- NOT "tried", so the honest "nothing was searched"
    # ValueError still fires rather than a misleading bare None. (This is the
    # exact scenario tests/test_free_logic_search.py's own
    # test_exhausted_candidate_budget_raises_instead_of_silently_returning_none
    # checks against the plain default -- reproduced here explicitly for both
    # settings of the new flag, since that file is outside this change's
    # ownership.)
    c = Constant("c")
    Px = Atom("P", [c])
    for sb in (True, False):
        with pytest.raises(ValueError, match="max_candidates"):
            fl.free_find_model(Px, max_size=1, max_candidates=1, symmetry_breaking=sb)


# ============================================================================
# Oracle (a), secondorder.py: _so_structures now enumerates its free symbols
# with the canonical generator; compare against the OLD raw-generator baseline
# reconstructed by hand (the module itself no longer offers a raw option --
# "reuse, no separate implementation" per the roadmap).
# ============================================================================

_SO_CONSTS = ["a", "b"]
_SO_VARS = [Variable("x"), Variable("y")]


def _random_so_term(rng: random.Random):
    return rng.choice(_SO_VARS) if rng.random() < 0.5 else Constant(rng.choice(_SO_CONSTS))


def _random_so_atom(rng: random.Random):
    # "P" will be SO-bound by the outer quantifier below; "R" stays a free
    # (structure-interpreted) predicate, so the free signature is non-trivial.
    return Atom(rng.choice(["P", "R"]), [_random_so_term(rng)])


def _random_so_body(rng: random.Random, depth: int):
    if depth <= 0 or rng.random() < 0.35:
        return _random_so_atom(rng)
    choice = rng.random()
    if choice < 0.2:
        return Not(_random_so_body(rng, depth - 1))
    if choice < 0.4:
        return And(_random_so_body(rng, depth - 1), _random_so_body(rng, depth - 1))
    if choice < 0.6:
        return Or(_random_so_body(rng, depth - 1), _random_so_body(rng, depth - 1))
    if choice < 0.75:
        return Implies(_random_so_body(rng, depth - 1), _random_so_body(rng, depth - 1))
    if choice < 0.85:
        return Iff(_random_so_body(rng, depth - 1), _random_so_body(rng, depth - 1))
    var = rng.choice(_SO_VARS)
    qtype = rng.choice(["∀", "∃"])
    return Quantifier(qtype, var, _random_so_body(rng, depth - 1))


def _random_so_formula(rng: random.Random, depth: int):
    body = _random_so_body(rng, depth)
    qtype = rng.choice(["∀", "∃"])
    return SecondOrderQuantifier(qtype, "P", 1, body)


def _so_model_exists_at_size(sentence, sig, k, use_canonical):
    domain = tuple(range(k))
    gen = mf._canonical_interpretations(sig, domain) if use_canonical else mf._interpretations(sig, domain)
    for constants, functions, predicates in gen:
        structure = Structure(domain, constants=constants, functions=functions, predicates=predicates)
        if so.holds(sentence, structure):
            return True
    return False


def test_secondorder_random_signatures_agree_at_each_size():
    rng = random.Random(20260919)
    checked = 0
    for _ in range(20):
        formula = _random_so_formula(rng, depth=2)
        sentence = mf._universal_closure(formula)
        sig = so._so_signature(sentence)
        for k in (1, 2):
            expected = _so_model_exists_at_size(sentence, sig, k, use_canonical=False)
            actual = _so_model_exists_at_size(sentence, sig, k, use_canonical=True)
            assert actual == expected, (
                f"size {k} mismatch on {formula.to_prover9()!r}: "
                f"unbroken={expected} canonical={actual}")
            checked += 1
    assert checked == 40


def test_so_find_model_result_is_independently_reverified():
    # Sanity that the public entry point, now backed by the canonical
    # generator, still only ever returns a genuine model -- re-checked with
    # secondorder.holds, the module's own independent evaluator.
    a = Constant("a")
    formula = SecondOrderQuantifier("∃", "P", 1, Atom("P", [a]))
    m = so.so_find_model(formula, max_size=2)
    assert m is not None
    assert so.holds(mf._universal_closure(formula), m) is True


# ============================================================================
# Adversarial-review fix: an EXACT analytic count of what the LNH generator
# yields, replacing the original implementation's unbounded "live count and
# break inside the loop" -- which had no O(1) pre-flight at all, so a signature
# with few or no constants (where LNH cannot reduce anything: only constants are
# canonicalized, functions/predicates stay fully exhaustive either way) paid to
# enumerate and model-check up to max_candidates candidates on EVERY domain size
# before find_model/free_find_model could even conclude a size didn't fit the
# budget -- turning what used to be an instant analytic skip into a severe,
# effectively unbounded slowdown (reproduced by the reviewer: >400s, where the
# unbroken exhaustive path took 0.3s). _lnh_constant_count / _canonical_candidate_count
# (modelfinder) and _canonical_constant_count / _canonical_candidate_count
# (free_logic) restore an O(1)-per-size analytic pre-flight, computed once and
# for all here to be EXACT (not just an upper bound), so a size is fully
# enumerated whenever it is tried and skipped in O(1) otherwise -- no live count
# loop is needed. The tests below check the counting formulas directly
# (independent of the live regression) and then the fix at the PUBLIC entry
# point (find_model / free_find_model), exactly the level the reviewer's
# "major" finding said was missing.
# ============================================================================

def test_lnh_constant_count_matches_brute_force_backtracking():
    """_lnh_constant_count(n, k) must equal the number of leaves the ACTUAL
    _lnh_choices backtracking recursion visits -- an independent brute-force
    route (walking _lnh_choices itself, never _canonical_interpretations),
    across a grid including two hand-checked values: n=2,k=2 -> 2 (the set
    partitions of a 2-element set: {ab} and {a|b}, both fit in <=2 blocks) and
    n=3,k=2 -> 4 (partitions of a 3-element set into <=2 blocks: {abc}, {ab|c},
    {ac|b}, {bc|a} -- excluding {a|b|c}, which needs 3 distinct domain values)."""
    def brute(n, k):
        count = 0
        def bt(i, next_new):
            nonlocal count
            if i == n:
                count += 1
                return
            for v in mf._lnh_choices(next_new, k):
                bt(i + 1, next_new + 1 if v == next_new else next_new)
        bt(0, 0)
        return count

    assert mf._lnh_constant_count(2, 2) == 2   # hand-checked (see docstring above)
    assert mf._lnh_constant_count(3, 2) == 4   # hand-checked (see docstring above)
    for n in range(0, 5):
        for k in range(1, 5):
            assert mf._lnh_constant_count(n, k) == brute(n, k), (n, k)


def test_canonical_candidate_count_matches_exact_enumeration():
    """_canonical_candidate_count must equal len(list(_canonical_interpretations(...)))
    EXACTLY (not merely an upper bound) for a mix of constant-only,
    function-only, predicate-only and mixed signatures, including the
    NO-CONSTANTS case the adversarial review's blocker turned on -- that is
    precisely what lets find_model's pre-flight check replace the old live
    count-and-break loop with an O(1) analytic check while still never
    truncating a size's search mid-generator."""
    cases = [
        (frozenset({"a", "b"}), frozenset(), frozenset(), 3),
        (frozenset({"a"}), frozenset({("f", 1)}), frozenset(), 2),
        (frozenset(), frozenset({("f", 2)}), frozenset({("P", 1)}), 2),
        (frozenset({"a", "b", "c"}), frozenset(), frozenset({("P", 1)}), 3),
        (frozenset(), frozenset(), frozenset({("P", 2)}), 3),
    ]
    for consts, funcs, preds, k in cases:
        sig = mf._Signature()
        sig.constants, sig.functions, sig.predicates = consts, funcs, preds
        domain = tuple(range(k))
        actual = sum(1 for _ in mf._canonical_interpretations(sig, domain))
        assert mf._canonical_candidate_count(sig, k) == actual, (consts, funcs, preds, k)


def test_free_logic_canonical_constant_count_matches_brute_force():
    """fl._canonical_constant_count's DP (which adds a "non-denoting" option per
    cell on top of modelfinder's _lnh_choices) checked against an independent
    brute-force walk of _canonical_constant_assignments's own backtracking
    shape, including the hand-checked n=1,k=1 -> 2 case (a single partial
    constant is either "c" -> the domain's one element, or omitted/non-denoting
    -- exactly 2 partial assignments)."""
    def brute(n, k):
        count = 0
        def bt(i, next_new):
            nonlocal count
            if i == n:
                count += 1
                return
            for v in (None,) + tuple(mf._lnh_choices(next_new, k)):
                bt(i + 1, next_new + 1 if (v is not None and v == next_new) else next_new)
        bt(0, 0)
        return count

    assert fl._canonical_constant_count(1, 1) == 2   # hand-checked (see docstring above)
    for n in range(0, 4):
        for k in range(1, 4):
            assert fl._canonical_constant_count(n, k) == brute(n, k), (n, k)


def test_free_logic_canonical_candidate_count_matches_exact_enumeration():
    """fl._canonical_candidate_count must equal
    len(list(_canonical_candidate_models(...))) EXACTLY, for both domain_split
    settings and including a NO-CONSTANTS, function/predicate-only signature --
    the shape the adversarial review's free_logic blocker turned on."""
    cases = [
        (["a", "b"], [], [], 2, "any"),
        (["a"], [("f", 1)], [], 2, "total"),
        ([], [("f", 1)], [("P", 1)], 2, "any"),
        (["a", "b"], [], [("P", 1)], 2, "total"),
    ]
    for const_names, func_sig, pred_sig, k, domain_split in cases:
        domain = tuple(range(k))
        actual = sum(1 for _ in fl._canonical_candidate_models(
            domain, const_names, func_sig, pred_sig, domain_split))
        predicted = fl._canonical_candidate_count(
            len(const_names), set(func_sig), set(pred_sig), k, domain_split)
        assert predicted == actual, (const_names, func_sig, pred_sig, k, domain_split)


def test_find_model_with_no_constants_stays_bounded_when_symmetry_breaking():
    """Regression guard, at the PUBLIC entry point, for the adversarial review's
    blocker: before the fix, find_model's symmetry_breaking=True branch had NO
    pre-flight skip at all -- it unconditionally live-counted through
    _canonical_interpretations, model-checking every candidate up to
    max_candidates, for every domain size. For a signature with NO constants
    (where LNH cannot reduce anything at all), that turned an instant analytic
    skip into a multi-minute-or-worse hang. A contradictory theory over a single
    binary function and no constants forces exhaustion of the FULL candidate
    space at every size before concluding None -- exactly the shape the review
    reproduced (reviewer's own numbers: 0.315s at symmetry_breaking=False vs.
    >400s, unfinished, at symmetry_breaking=True). It must now be comparably
    fast under both settings.
    """
    x, y = Variable("x"), Variable("y")
    fxy, fyx = Function("f", [x, y]), Function("f", [y, x])
    # HAND CHECK: "f is commutative everywhere" AND "f is non-commutative
    # somewhere" is a straight propositional contradiction (universal vs.
    # existential negation of the same equation) -- unsatisfiable at every
    # domain size, so both search modes must exhaust their full space and
    # agree on None.
    comm = Quantifier("∀", x, Quantifier("∀", y, Atom("=", [fxy, fyx])))
    noncomm = Quantifier("∃", x, Quantifier("∃", y, Not(Atom("=", [fxy, fyx]))))
    formula = And(comm, noncomm)

    times = {}
    for sb in (False, True):
        t0 = time.time()
        result = mf.find_model([formula], max_size=4, symmetry_breaking=sb)
        times[sb] = time.time() - t0
        assert result is None

    # The unfixed code did not finish this within a 400s timeout; the fixed
    # code finishes in well under a second locally -- 5s leaves generous
    # headroom for a slow/loaded CI machine while still catching any
    # reintroduction of the unbounded live-count loop.
    assert times[True] < 5.0, times


def test_free_find_model_with_no_constants_stays_bounded_when_symmetry_breaking():
    """The same regression guard as above, for free_logic._search's identical
    hand-ported defect (the reviewer's second blocker), fixed the same way via
    fl._canonical_candidate_count."""
    x, y = Variable("x"), Variable("y")
    fxy, fyx = Function("f", [x, y]), Function("f", [y, x])
    comm = Quantifier("∀", x, Quantifier("∀", y, Atom("=", [fxy, fyx])))
    noncomm = Quantifier("∃", x, Quantifier("∃", y, Not(Atom("=", [fxy, fyx]))))
    formula = And(comm, noncomm)

    times = {}
    for sb in (False, True):
        t0 = time.time()
        result = fl.free_find_model(formula, max_size=3, symmetry_breaking=sb)
        times[sb] = time.time() - t0
        # HAND CHECK: even under free-logic's non-denoting escape hatch, the
        # theory stays unsatisfiable -- comm forces EVERY existing pair to have
        # f denoting and symmetric, so noncomm's existential witness (which
        # ranges over the same existing domain) can never be satisfied except
        # by an empty existing domain, where noncomm itself is vacuously false.
        assert result is None

    assert times[True] < 5.0, times
