"""Tests for unicode_fol_kit.fol.simplify_check.

Every expected value is hand-derived in a comment above the assertion, never
read off from running the code first. Two independent things are checked
(see the module docstring in simplify_check.py for the full rationale):

* ``simplify_for_checking`` — the "always safe" rules (duplicate conjuncts/
  disjuncts, ``t=t``, vacuous quantifiers, double negation) plus the
  ``all_different=True`` rule that is sound only under the ChEBI2FOL model
  checker's own "separately introduced existential variables are already
  distinct" convention (never under plain classical semantics — that is
  exactly why it defaults to ``False`` and is tested both ways below).
* ``count_from_existential_chain`` / ``expand_count`` — a genuine classical
  equivalence (``∃x_0…∃x_{n-1}(⋀φ(x_i) ∧ ⋀_{i<j} x_i≠x_j) ≡ Count("ge",n,x,φ)``
  because the former IS ``Count._expand``'s own encoding), checked with Z3
  (unbounded-domain validity of the biconditional, not just small models) for
  n=2,3,4 in both directions, plus the literal hasAtLeast40Carbons example
  from the paper (40 variables, C(40,2)=780 pairwise inequalities).

Recursion note: the n=40 example builds a genuinely 820-conjunct, left-
nested ∧-chain (exactly how straightforward code generates a flat n-ary
conjunction — and exactly the shape the module's own docstring calls out as
a real recursion-limit risk for a NAIVELY recursive tree walker). simplify_
check's own flatten/rebuild is iterative for this reason, but the vacuity
check it calls into (``free_variables``, in the shared, not-owned-by-this-
module AST layer) is an ordinary recursive walk, so the two n=40 tests widen
Python's recursion limit for their duration.
"""

import sys
from contextlib import contextmanager

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Quantifier, Variable, Constant, Number, Count,
    SortedQuantifier,
)
from unicode_fol_kit.fol.simplify_check import (
    SimplifyResult, simplify_for_checking,
    count_from_existential_chain, expand_count,
)
from unicode_fol_kit.atp.z3_equivalence import formulas_are_equivalent


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


x, y, z = Variable("x"), Variable("y"), Variable("z")
a = Constant("a")


def _conj(*parts):
    """Left-associative And-fold — the shape naive code generation produces."""
    result = parts[0]
    for p in parts[1:]:
        result = And(result, p)
    return result


def _build_chain(n, predicate, varprefix):
    """The literal ChEBI2FOL distinct-witnesses pattern: n existentially
    quantified variables, each satisfying ``predicate``, plus all C(n,2)
    pairwise inequalities — left-nested, exactly as straightforward code
    (or an LLM writing out every pair by hand) would emit it. Returns
    (formula, [the n Variable nodes, outermost-bound first])."""
    vs = [Variable(f"{varprefix}{i}") for i in range(n)]
    conjuncts = [Atom(predicate, [v]) for v in vs]
    for i in range(n):
        for j in range(i + 1, n):
            conjuncts.append(Atom("≠", [vs[i], vs[j]]))
    body = _conj(*conjuncts)
    formula = body
    for v in reversed(vs):
        formula = Quantifier("∃", v, formula)
    return formula, vs


@contextmanager
def _wide_recursion_limit(n=10_000):
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, n))
    try:
        yield
    finally:
        sys.setrecursionlimit(old)


# ---------------------------------------------------------------------------
# Always-on rules: trivial equality (only inside a conjunction).
# ---------------------------------------------------------------------------

def test_trivial_equality_dropped_from_conjunction():
    # x=x is reflexively true for ANY assignment, so φ ∧ (x=x) ≡ φ.
    result = simplify_for_checking(And(Atom("=", [x, x]), P(a)))
    assert result.changed is True
    assert len(result.removed) == 1
    assert result.simplified == P(a)


def test_trivial_equality_alone_is_left_untouched():
    # A lone "x=x" is the WHOLE formula here (not a conjunct of anything) —
    # there is nothing to fold it into (no True node in this kit), so it must
    # be left exactly as it is rather than vanish into an empty tree.
    formula = Atom("=", [x, x])
    result = simplify_for_checking(formula)
    assert result.changed is False
    assert result.removed == ()
    assert result.simplified == formula


def test_all_conjuncts_trivial_keeps_exactly_one():
    # Both conjuncts are trivially true; dropping BOTH would leave nothing,
    # so exactly one survives (the first, by construction) and the second
    # is dropped as redundant given the first already witnesses "true".
    formula = And(Atom("=", [x, x]), Atom("=", [y, y]))
    result = simplify_for_checking(formula)
    assert result.changed is True
    assert len(result.removed) == 1
    assert result.simplified == Atom("=", [x, x])


def test_trivial_equality_not_dropped_from_a_disjunction():
    # Dropping a trivially-true DISJUNCT would be WRONG: A ∨ (t=t) ≡ True,
    # not A — so this rule must never fire inside Or.
    formula = Or(Atom("=", [x, x]), P(a))
    result = simplify_for_checking(formula)
    assert result.changed is False
    assert result.simplified == formula


# ---------------------------------------------------------------------------
# Always-on rules: idempotence (duplicate conjuncts/disjuncts).
# ---------------------------------------------------------------------------

def test_duplicate_conjunct_removed():
    result = simplify_for_checking(And(P(a), P(a)))
    assert result.simplified == P(a)
    assert len(result.removed) == 1
    assert "duplicate" in result.removed[0]


def test_duplicate_conjunct_removed_across_branches():
    # Flattened this is [P(a), Q(b), P(a), R(c)] — the SECOND P(a) is a
    # duplicate even though it sits in a different And-branch than the first.
    b, c = Constant("b"), Constant("c")
    formula = And(And(P(a), Q(b)), And(P(a), Atom("R", [c])))
    result = simplify_for_checking(formula)
    assert result.simplified == And(And(P(a), Q(b)), Atom("R", [c]))
    assert len(result.removed) == 1


def test_duplicate_disjunct_removed():
    result = simplify_for_checking(Or(P(a), P(a)))
    assert result.simplified == P(a)
    assert len(result.removed) == 1


# ---------------------------------------------------------------------------
# Always-on rules: vacuous quantifiers, double negation.
# ---------------------------------------------------------------------------

def test_vacuous_existential_removed():
    result = simplify_for_checking(Quantifier("∃", x, P(a)))  # x not in P(a)
    assert result.simplified == P(a)
    assert result.changed is True
    assert len(result.removed) == 1


def test_vacuous_universal_removed():
    result = simplify_for_checking(Quantifier("∀", x, P(a)))
    assert result.simplified == P(a)
    assert result.changed is True


def test_non_vacuous_quantifier_kept():
    formula = Quantifier("∃", x, P(x))
    result = simplify_for_checking(formula)
    assert result.simplified == formula
    assert result.changed is False


def test_double_negation_collapsed():
    result = simplify_for_checking(Not(Not(P(a))))
    assert result.simplified == P(a)
    assert len(result.removed) == 1


def test_triple_negation_collapses_to_single_negation():
    # ¬¬¬P(a): the inner ¬¬ collapses to P(a) (one removal logged), leaving
    # the outer ¬ with nothing further to cancel against — ¬¬¬P(a) ≡ ¬P(a).
    result = simplify_for_checking(Not(Not(Not(P(a)))))
    assert result.simplified == Not(P(a))
    assert len(result.removed) == 1


# ---------------------------------------------------------------------------
# all_different=True: redundant pairwise inequality between separately
# existentially-bound variables — and its precise boundaries.
# ---------------------------------------------------------------------------

def _two_witness_chain(extra=None):
    """∃x∃y (c(x) ∧ c(y) ∧ x≠y [∧ extra])."""
    parts = [Atom("c", [x]), Atom("c", [y]), Atom("≠", [x, y])]
    if extra is not None:
        parts.append(extra)
    return Quantifier("∃", x, Quantifier("∃", y, _conj(*parts)))


def test_all_different_true_removes_ne_between_existentials():
    formula = _two_witness_chain()
    result = simplify_for_checking(formula, all_different=True)
    expected = Quantifier("∃", x, Quantifier("∃", y,
                                              And(Atom("c", [x]), Atom("c", [y]))))
    assert result.simplified == expected
    assert len(result.removed) == 1


def test_all_different_false_leaves_the_same_formula_untouched():
    # Default semantics: no assumption of distinctness, so x≠y stays — and
    # since NOTHING was removed anywhere in the tree, the rebuilt formula is
    # byte-for-byte identical to the input (see _rebuild_like).
    formula = _two_witness_chain()
    result = simplify_for_checking(formula)  # all_different=False (default)
    assert result.changed is False
    assert result.removed == ()
    assert result.simplified == formula


def test_all_different_ignores_an_extra_relational_literal():
    # bond(x,y) additionally relates the two witnesses; simplify_for_checking
    # (unlike count_from_existential_chain) does not require "nothing else in
    # the chain" — it only removes the ≠ LITERAL itself, which is sound
    # regardless of what else is asserted about x and y.
    formula = _two_witness_chain(extra=Atom("bond", [x, y]))
    result = simplify_for_checking(formula, all_different=True)
    expected = Quantifier("∃", x, Quantifier("∃", y,
        And(And(Atom("c", [x]), Atom("c", [y])), Atom("bond", [x, y]))))
    assert result.simplified == expected
    assert len(result.removed) == 1


def test_all_different_not_applied_across_a_universally_bound_variable():
    # x is ∀-bound here, not ∃-bound — the "separately introduced existential
    # variables are already distinct" convention says nothing about it.
    formula = Quantifier("∀", x, And(
        Atom("c", [x]),
        Quantifier("∃", y, And(Atom("c", [y]), Atom("≠", [x, y]))),
    ))
    result = simplify_for_checking(formula, all_different=True)
    assert result.changed is False
    assert result.simplified == formula


def test_all_different_not_applied_to_inequality_with_a_constant():
    formula = Quantifier("∃", x, And(Atom("c", [x]), Atom("≠", [x, a])))
    result = simplify_for_checking(formula, all_different=True)
    assert result.changed is False
    assert result.simplified == formula


def test_all_different_not_applied_to_self_inequality():
    # x≠x is a contradiction, not "two separately-bound variables" — leaving
    # it alone (rather than treating it as somehow redundant) is the
    # conservative, correct choice.
    formula = Quantifier("∃", x, And(Atom("c", [x]), Atom("≠", [x, x])))
    result = simplify_for_checking(formula, all_different=True)
    assert result.changed is False
    assert result.simplified == formula


# ---------------------------------------------------------------------------
# Regression tests for Finding 1: the generic structural fallback must
# SHADOW (remove from ``binders``) the bound-variable name of a non-
# Quantifier binder (Count/Cardinality/SortedQuantifier/SortedCount/
# SortedCardinality/Lambda) while descending into its body — otherwise a
# same-named OUTER ∃ leaks its "exists" classification into a name that,
# inside the binder, actually refers to something else entirely.
# ---------------------------------------------------------------------------

def test_all_different_true_does_not_cross_a_counts_own_shadowing():
    # ∃x∃y ( c(x) ∧ c(y) ∧ Count("ge", 2, x, d(x) ∧ x≠y) )
    #
    # Count's OWN bound variable is also named "x" — SAME name as the outer
    # ∃x. Inside Count's matrix, "x" is COUNT's bound variable (it shadows
    # the outer ∃x); "y" is genuinely still the outer ∃y (free inside
    # Count's scope). The x≠y literal here means "this candidate x differs
    # from y" — NOT "two separately ∃-bound witnesses are distinct" (the
    # all_different convention _is_redundant_all_diff_ne is meant to
    # recognise), so it must NOT be dropped: Count("ge",2,x, d(x)∧x≠y)
    # ("at least 2 individuals satisfying d that differ from y") and
    # Count("ge",2,x, d(x)) ("at least 2 individuals satisfying d, period")
    # are NOT the same claim — e.g. a structure with exactly 2 d-satisfying
    # individuals, one of which IS y, makes the first FALSE (only 1 of them
    # differs from y) and the second TRUE.
    #
    # Hand-derived, BEFORE the fix: the generic structural fallback recursed
    # into Count's `formula` field with the SAME `binders` dict the outer
    # ∃x/∃y chain had already built (binders={"x":"exists","y":"exists"}),
    # never removing the shadowed "x". So when that recursion reached the
    # nested And(d(x), x≠y) inside Count's own matrix, `_filter_and_
    # conjuncts` saw binders["x"]=="exists" (stale — actually the OUTER x,
    # not Count's own bound x) and binders["y"]=="exists" (correctly the
    # outer y) and wrongly treated x≠y as "two separately ∃-bound
    # witnesses" — dropping it and leaving Count("ge",2,x,d(x)) behind.
    # That is unsound: it silently changes what the formula asserts.
    inner = And(Atom("d", [x]), Atom("≠", [x, y]))
    count_node = Count("ge", Number(2), x, inner)
    formula = Quantifier("∃", x, Quantifier("∃", y,
        And(And(Atom("c", [x]), Atom("c", [y])), count_node)))

    result = simplify_for_checking(formula, all_different=True)

    counts = [n for n in result.simplified.walk() if isinstance(n, Count)]
    assert len(counts) == 1
    assert counts[0].formula == inner  # the x≠y literal must survive intact
    assert result.changed is False
    assert result.removed == ()


def test_all_different_true_does_not_cross_a_sorted_quantifiers_own_shadowing():
    # Same shadowing scenario as above, but via a SortedQuantifier (a
    # distinct class from Quantifier, per this module's own generic
    # fallback — see its docstring) instead of Count, to confirm the fix
    # generalises across every class in _SINGLE_VAR_BINDER_FIELDS and is not
    # a Count-specific special case.
    #
    # ∃x∃y ( c(x) ∧ c(y) ∧ (∃x:S (d(x) ∧ x≠y)) )
    #
    # The inner SortedQuantifier's own "x" shadows the outer ∃x; "y" is
    # still the outer ∃y. As above, dropping x≠y would silently change
    # "∃x:S (d(x) ∧ x differs from y)" into "∃x:S d(x)" — not equivalent.
    inner = And(Atom("d", [x]), Atom("≠", [x, y]))
    sorted_q = SortedQuantifier("∃", x, "S", inner)
    formula = Quantifier("∃", x, Quantifier("∃", y,
        And(And(Atom("c", [x]), Atom("c", [y])), sorted_q)))

    result = simplify_for_checking(formula, all_different=True)

    sorted_qs = [n for n in result.simplified.walk() if isinstance(n, SortedQuantifier)]
    assert len(sorted_qs) == 1
    assert sorted_qs[0].formula == inner
    assert result.changed is False
    assert result.removed == ()


# ---------------------------------------------------------------------------
# Idempotence, and a formula exercising every rule at once (with a second-
# order effect: removing x≠y leaves y with no remaining occurrence, so the
# ∃y around it becomes vacuous too, on the SAME pass).
# ---------------------------------------------------------------------------

def test_idempotent_and_composes_across_rule_kinds():
    # ∃x∃y ( c(x) ∧ c(x) ∧ (x=x) ∧ ¬¬P(a) ∧ x≠y ∧ ∃z Q(a) )
    #
    # Per-leaf simplification (before dedupe/filtering):
    #   c(x), c(x)            -> unchanged, unchanged
    #   x=x                    -> unchanged (removed only at the filter step)
    #   ¬¬P(a)                 -> P(a)                          [1 removal]
    #   x≠y                    -> unchanged (removed only at the filter step)
    #   ∃z Q(a)  (z not in Q(a)) -> Q(a)                        [1 removal]
    # -> parts = [c(x), c(x), x=x, P(a), x≠y, Q(a)]
    #
    # Dedupe: second c(x) is a duplicate of the first                [1 removal]
    # -> kept = [c(x), x=x, P(a), x≠y, Q(a)]
    #
    # all_different filter: x=x is trivial (drop), x≠y is redundant
    # (x,y both ∃-bound, drop)                                    [2 removals]
    # -> kept = [c(x), P(a), Q(a)]  ==  And(And(c(x),P(a)),Q(a))
    #
    # Back at ∃y: y no longer occurs free in the new body (its only
    # occurrence, x≠y, is gone) -> ∃y is now itself vacuous          [1 removal]
    # Back at ∃x: x DOES occur free (c(x)) -> ∃x is kept.
    #
    # Total removed: 1+1+1+2+1 = 6. Result: ∃x( c(x) ∧ P(a) ∧ Q(a) ).
    formula = Quantifier("∃", x, Quantifier("∃", y, _conj(
        Atom("c", [x]), Atom("c", [x]), Atom("=", [x, x]),
        Not(Not(P(a))), Atom("≠", [x, y]),
        Quantifier("∃", z, Q(a)),
    )))
    first = simplify_for_checking(formula, all_different=True)
    expected = Quantifier("∃", x, And(And(Atom("c", [x]), P(a)), Q(a)))
    assert first.simplified == expected
    assert len(first.removed) == 6
    assert first.changed is True

    second = simplify_for_checking(first.simplified, all_different=True)
    assert second.changed is False
    assert second.removed == ()
    assert second.simplified == first.simplified


# ---------------------------------------------------------------------------
# The literal paper example: hasAtLeast40Carbons (40 variables, C(40,2)=780
# pairwise inequalities). Appendix B.3 of ChEBI2FOL (NeSy 2026).
# ---------------------------------------------------------------------------

def test_paper_example_40_carbons_recognized_as_count():
    with _wide_recursion_limit():
        formula, vs = _build_chain(40, "c", "x")
        recognized = count_from_existential_chain(formula)
    assert recognized == Count("ge", Number(40), vs[0], Atom("c", [vs[0]]))


def test_paper_example_40_carbons_all_different_removes_exactly_780():
    with _wide_recursion_limit():
        formula, _ = _build_chain(40, "c", "x")

        result_true = simplify_for_checking(formula, all_different=True)
        assert result_true.changed is True
        assert len(result_true.removed) == 780  # binomial(40, 2)
        remaining_ne = [n for n in result_true.simplified.walk()
                         if isinstance(n, Atom) and n.predicate == "≠"]
        assert remaining_ne == []
        remaining_c = [n for n in result_true.simplified.walk()
                        if isinstance(n, Atom) and n.predicate == "c"]
        assert len(remaining_c) == 40

        result_false = simplify_for_checking(formula)  # all_different=False
        assert result_false.changed is False
        assert result_false.removed == ()
        assert result_false.simplified == formula


# ---------------------------------------------------------------------------
# count_from_existential_chain: conservative refusal (Node|None contract).
# ---------------------------------------------------------------------------

def test_count_from_chain_rejects_an_extra_relational_literal():
    # ∃x∃y (c(x) ∧ c(y) ∧ bond(x,y)): 3 literals happens to match the
    # expected count n+C(n,2)=2+1=3, but the third slot is bond(x,y), not
    # the required x≠y — rewriting would silently drop the bond fact.
    formula = Quantifier("∃", x, Quantifier("∃", y,
        _conj(Atom("c", [x]), Atom("c", [y]), Atom("bond", [x, y]))))
    assert count_from_existential_chain(formula) is None


def test_count_from_chain_rejects_mismatched_predicates():
    formula = Quantifier("∃", x, Quantifier("∃", y,
        _conj(Atom("c", [x]), Atom("o", [y]), Atom("≠", [x, y]))))
    assert count_from_existential_chain(formula) is None


def test_count_from_chain_rejects_inequality_with_a_constant():
    formula = Quantifier("∃", x, Quantifier("∃", y,
        _conj(Atom("c", [x]), Atom("c", [y]), Atom("≠", [x, a]))))
    assert count_from_existential_chain(formula) is None


def test_count_from_chain_rejects_non_chain_input():
    assert count_from_existential_chain(P(a)) is None


def test_count_from_chain_rejects_a_universal_interrupting_the_prefix():
    formula = Quantifier("∃", x, Quantifier("∀", y, Atom("c", [x])))
    assert count_from_existential_chain(formula) is None


# ---------------------------------------------------------------------------
# expand_count: reuses Count._expand (checked structurally, hand-derived).
# ---------------------------------------------------------------------------

def test_expand_count_matches_hand_derived_shape_n2():
    # Count._expand for n=Count("ge",2,x,c(x)):
    #   avoid = free_vars(c(x)) | {"x"} = {"x"}
    #   fresh(2) -> "x_0" (not in avoid), then "x_1" (not in {"x","x_0"})
    #   at_least(2): conjuncts = [c(x_0), c(x_1), x_0≠x_1]
    #   _balanced_and([c(x_0),c(x_1),x_0≠x_1]): pairs (0,1) merge, odd one
    #     (x_0≠x_1) appended -> [And(c(x_0),c(x_1)), x_0≠x_1], then merges to
    #     And(And(c(x_0),c(x_1)), x_0≠x_1)
    #   wrapped in reversed(ws) order: ∃x_0(∃x_1(body))
    count = Count("ge", Number(2), Variable("x"), Atom("c", [Variable("x")]))
    x0, x1 = Variable("x_0"), Variable("x_1")
    expected = Quantifier("∃", x0, Quantifier("∃", x1,
        And(And(Atom("c", [x0]), Atom("c", [x1])), Atom("≠", [x0, x1]))))
    assert expand_count(count) == expected
    assert expand_count(count) == count._expand()


def test_expand_count_reaches_a_count_nested_inside_other_structure():
    formula = And(P(a), Count("ge", Number(1), Variable("v"),
                               Atom("c", [Variable("v")])))
    result = expand_count(formula)
    assert isinstance(result, And)
    assert not any(isinstance(n, Count) for n in result.walk())


# ---------------------------------------------------------------------------
# Z3 equivalence, both directions, n=2,3,4 (small enough for an unbounded-
# domain validity check, per the module's documented soundness story).
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("n", [2, 3, 4])
def test_chain_count_round_trip_is_z3_equivalent_both_directions(n):
    # Direction 1: hand-built chain -> recognize -> Count -> expand -> compare
    # to the ORIGINAL chain. The round-tripped formula necessarily differs in
    # bracketing/variable-naming from the hand-built one (expand_count uses
    # Count._expand's own "x_i" fresh names), so structural equality is not
    # meaningful here — Z3 is asked to prove the biconditional valid instead.
    chain, vs = _build_chain(n, "c", "w")
    recognized = count_from_existential_chain(chain)
    assert recognized == Count("ge", Number(n), vs[0], Atom("c", [vs[0]]))
    round_tripped = expand_count(recognized)
    assert formulas_are_equivalent(chain, round_tripped) is True

    # Direction 2: Count -> expand -> recognize -> compare the RECOVERED
    # Count to the original Count (different bound-variable name on purpose,
    # to make sure alpha-renaming plays no role in either function).
    count = Count("ge", Number(n), Variable("v"), Atom("c", [Variable("v")]))
    expanded = expand_count(count)
    recovered = count_from_existential_chain(expanded)
    assert recovered is not None
    assert formulas_are_equivalent(count, recovered) is True
