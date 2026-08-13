"""Tests for redundancy elimination in the resolution prover
(unicode_fol_kit.atp.resolution): tautology deletion and forward/backward
clause subsumption.

Every expected value is hand-derived (see the comment above each assertion for
the derivation), not taken from running the code first. Four things are
checked:

- ``_match``: one-sided matching binds only the PATTERN side; the target's own
  structure (including any variables it happens to contain) is never
  instantiated.
- ``_subsumes``: clause subsumption built on top of ``_match``, including a
  case engineered to fail specifically because of a REPEATED pattern
  variable (a place a naive, non-backtracking matcher could wrongly succeed).
- ``_is_tautology`` and the fact that deleting tautologies from a saturation
  run never costs completeness (the same refutations still go through).
- A measurable case: a clause set with many redundant (subsumed) seed clauses
  that ``refute`` closes within a tight ``max_steps`` budget specifically
  because subsumption stops them from ever being explored — with a hand-argued
  lower bound on how many steps the un-pruned search would need instead.

Regression protection for the surrounding module lives in test_resolution.py
and test_resolution_check.py (soundness/entailment batteries); both must stay
green, since neither tautology deletion nor subsumption may change what
``prove``/``refute``/``is_valid_resolution`` return — only how many steps they
need to get there.
"""

from unicode_fol_kit.fol.nodes import Atom, Not, Variable, Constant
from unicode_fol_kit.atp.resolution import (
    refute, _match, _subsumes, _is_tautology,
)


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


def R(*args):
    return Atom("R", list(args))


x, y = Variable("x"), Variable("y")
a, b, c = Constant("a"), Constant("b"), Constant("c")


# ---------------------------------------------------------------------------
# _match: one-sided matching (only the pattern side is bound)
# ---------------------------------------------------------------------------

def test_match_binds_pattern_variable_to_ground_target():
    # P(x,a) matched against P(b,a): predicate/arity agree; x is a pattern
    # variable so it is free to bind to b; the second slot is already ground
    # on both sides and equal (a == a), so the match succeeds with x -> b.
    subst = _match(P(x, a), P(b, a))
    assert subst == {"x": b}


def test_match_does_not_bind_the_target_side():
    # P(a,x) against P(y,b): first slot is pattern-ground Constant a versus
    # target-side Variable y. One-sided matching only binds PATTERN
    # variables — the target's y is opaque, not something the matcher may
    # instantiate — so a (a Constant) simply fails to equal y (a Variable):
    # no substitution can make them coincide. Hence no match, even though a
    # two-sided unifier (unify(a, y)) would happily bind y := a.
    assert _match(P(a, x), P(y, b)) is None


def test_match_repeated_pattern_variable_must_stay_consistent():
    # P(x,x) against P(a,a): the second occurrence of x must bind to the same
    # term as the first (a), which it does, so the match succeeds.
    assert _match(P(x, x), P(a, a)) == {"x": a}
    # P(x,x) against P(a,b): the second occurrence of x would have to be both
    # a (from the first slot) and b (from the second) — inconsistent, so the
    # match fails.
    assert _match(P(x, x), P(a, b)) is None


def test_match_predicate_and_arity_must_agree():
    assert _match(P(a), Q(a)) is None          # different predicate
    assert _match(P(a), P(a, b)) is None        # different arity


def test_match_ground_atoms_require_exact_equality():
    assert _match(P(a, b), P(a, b)) == {}
    assert _match(P(a, b), P(a, c)) is None


# ---------------------------------------------------------------------------
# _subsumes: clause subsumption on top of _match
# ---------------------------------------------------------------------------

def test_subsumes_unit_clause_into_a_disjunction():
    # {P(x)} subsumes {P(a), Q(b)}: x -> a makes the single pattern literal
    # equal to the first target literal, which is enough (subsumption needs
    # every pattern literal covered by SOME target literal, not the whole
    # target clause explained).
    assert _subsumes(frozenset({P(x)}), frozenset({P(a), Q(b)})) is True


def test_subsumes_two_literal_pattern_into_three_literal_target():
    # {P(x), Q(x)} subsumes {P(a), Q(a), R(c)}: the single binding x -> a
    # simultaneously makes P(x) equal P(a) and Q(x) equal Q(a); R(c) is
    # simply not needed to cover the pattern, and subsumption does not
    # require it to be.
    pattern = frozenset({P(x), Q(x)})
    target = frozenset({P(a), Q(a), R(c)})
    assert _subsumes(pattern, target) is True


def test_subsumes_fails_when_a_pattern_literal_has_no_partner():
    # {P(x), Q(y)} does NOT subsume {P(a)}: P(x) can bind (x -> a), but Q(y)
    # has no literal of predicate Q anywhere in the singleton target to match
    # against — the search tries every target literal for Q(y) (here, just
    # P(a)) and every one fails on the predicate check. This is a genuine
    # non-subsumption, not merely a length short-circuit: refute()'s callers
    # additionally skip the _subsumes call whenever len(pattern) >
    # len(target) as a cheap optimisation for exactly this kind of hopeless
    # case, but _subsumes itself must (and does) reject it on the merits.
    assert _subsumes(frozenset({P(x), Q(y)}), frozenset({P(a)})) is False


def test_subsumes_no_false_positive_from_a_repeated_variable():
    # {R(x,x)} does NOT subsume {R(a,b)}: matching R(x,x) against R(a,b)
    # would need x -> a (from the first argument) AND x -> b (from the
    # second) at once — inconsistent, so no substitution closes the pattern
    # literal, and _subsumes correctly reports False. A matcher that bound
    # each occurrence of x independently (instead of threading one shared
    # substitution) would wrongly report True here.
    assert _subsumes(frozenset({R(x, x)}), frozenset({R(a, b)})) is False
    # The consistent case: {R(x,x)} DOES subsume {R(a,a)} (x -> a satisfies
    # both occurrences), confirming the failure above is specifically about
    # the inconsistency, not some unrelated bug.
    assert _subsumes(frozenset({R(x, x)}), frozenset({R(a, a)})) is True


def test_subsumes_respects_polarity():
    # {P(x)} does not subsume {¬P(a)}: same atom shape, opposite polarity —
    # a positive pattern literal may only be matched against a positive
    # target literal.
    assert _subsumes(frozenset({P(x)}), frozenset({Not(P(a))})) is False


# ---------------------------------------------------------------------------
# _is_tautology
# ---------------------------------------------------------------------------

def test_is_tautology_identical_atom():
    # {P(x), ¬P(x)}: same atom (same predicate, same argument x) with both
    # polarities present — valid in every interpretation.
    assert _is_tautology(frozenset({P(x), Not(P(x))})) is True


def test_is_tautology_false_for_syntactically_different_atoms():
    # {P(x), ¬P(y)}: different variable names make these different Atom
    # objects syntactically (x != y are not identified without an
    # instantiation this check deliberately does not perform), so this is
    # NOT flagged as a tautology, matching the module's documented scope.
    assert _is_tautology(frozenset({P(x), Not(P(y))})) is False


def test_is_tautology_false_for_a_genuinely_unsatisfiable_pair_of_clauses():
    # A clause containing only one polarity of P is never a tautology, no
    # matter how many literals — sanity check that _is_tautology needs BOTH
    # polarities of the SAME atom, not just repetition.
    assert _is_tautology(frozenset({P(a), P(b)})) is False


def test_tautology_deletion_does_not_cost_completeness():
    # {P} and {¬P} alone already refute the set (P, ¬P resolve to the empty
    # clause). Adding an unrelated tautology {Q, ¬Q} must not prevent that:
    # deleting it (it is filtered out of the seed set before saturation
    # starts, per refute()'s docstring) removes a clause that could never
    # have contributed to a refutation in the first place (a tautology is
    # valid in every model, so it can never help derive falsity).
    clauses = {
        frozenset({P()}),
        frozenset({Not(P())}),
        frozenset({Q(), Not(Q())}),  # tautology; irrelevant to the proof
    }
    assert refute(clauses) is True


# ---------------------------------------------------------------------------
# Measurable case: subsumption keeps a redundancy-heavy set inside budget
# ---------------------------------------------------------------------------

def test_subsumption_keeps_redundant_clause_set_within_tight_budget():
    # Ground propositional atoms (0-ary predicates) P, G, Q0..Q19.
    Patom, Gatom = Atom("P", []), Atom("G", [])
    n = 20
    qs = [Atom(f"Q{i}", []) for i in range(n)]

    core = frozenset({Not(Patom), Gatom})            # ¬P ∨ G   ("P implies G")
    fact_p = frozenset({Patom})                      # P
    neg_goal = frozenset({Not(Gatom)})                # ¬G
    # n near-duplicates of `core`, each with one extra, otherwise-inert
    # literal Qi tacked on. Every one of these is a strict superset of
    # `core` as a literal set (no substitution even needed — the match is
    # the identity on ¬P and G), so `core` subsumes every padded_i.
    padded = [frozenset({Not(Patom), Gatom, qs[i]}) for i in range(n)]

    for pc in padded:
        assert _subsumes(core, pc) is True  # confirms the mechanism in play

    clauses = {core, fact_p, neg_goal} | set(padded)

    # WITH subsumption (the current refute()): at seeding, `core` (length 2)
    # sorts before every `padded_i` (length 3), so by the time each padded_i
    # is considered, `core` is already kept and forward-subsumes it — none
    # of the n padded clauses ever enter the kept set. What remains is just
    # {P}, {¬G}, {¬P,G}: P resolves with core to give {G} (1 step), ¬G
    # resolves with core to give {¬P} (1 step), and either {G} meets {¬G} or
    # {¬P} meets {P} to close the empty clause — a handful of steps in any
    # processing order, comfortably inside a tight budget.
    assert refute(clauses, max_steps=10) is True

    # Re-running must give the identical result (refute()'s documented
    # determinism: processing order is a function of clause CONTENT, not of
    # hash-seed-dependent frozenset iteration).
    assert refute(clauses, max_steps=10) is True

    # Hand argument for why plain saturation (no subsumption) would blow this
    # same budget: without forward subsumption, all n padded_i clauses also
    # survive seeding and sit in kept_list alongside `core`. The FIRST time
    # {P} is processed as the given clause, it is resolved against every
    # member of kept_list in turn (the outer "for other in kept_list" loop in
    # refute() has no early exit besides deriving the empty clause) — and P
    # resolves against EVERY padded_i (P is the exact complement of the ¬P
    # literal each one carries), producing n distinct resolvents {G, Qi},
    # i = 0..19. Each of those is a genuine step (`steps += 1` fires once per
    # resolvent actually produced by `_resolvents`, unconditionally). That is
    # 20 unavoidable, wasted steps from this one interaction alone —
    # already exceeding max_steps=10 before the search could even move on to
    # processing {¬G} and reach the empty clause. Subsumption is precisely
    # what prevents those 20 padded clauses from ever being kept, hence from
    # ever being resolved against, hence from ever costing a step.
