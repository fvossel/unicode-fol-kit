"""Tests for the second-order circumscription axiom
(unicode_fol_kit.semantics.nonmonotonic.circumscription_formula /
circumscription_entails_so), cross-checked against the bounded minimal-model
search (minimal_entails) already tested in test_new_subsystems.py.

The formal anchor is DIFFERENTIAL: for each hand-picked case,

    minimal_entails(premises, conclusion, circumscribed, max_size=N)
        ==
    so_is_valid_finite(circumscription_entails_so(premises, circumscribed, conclusion),
                       max_size=N)

must agree — one enumerates minimal models directly, the other enumerates
EVERY finite structure and checks the second-order minimality axiom; McCarthy's
theorem says these decide the same relation, so any disagreement is a bug.
Every case's EXPECTED verdict is derived by hand in a comment before either
oracle is consulted.
"""

from unicode_fol_kit import (
    MSFLParser, Atom, And, Not, Implies, Or, Quantifier, Variable, Constant,
    SecondOrderQuantifier,
)
from unicode_fol_kit.semantics.nonmonotonic import (
    minimal_entails, circumscription_formula, circumscription_entails_so,
)
from unicode_fol_kit.semantics.secondorder import so_is_valid_finite

FOL = MSFLParser()
p = FOL.parse

#: Bound shared by both oracles in every differential check below (kept small:
#: the SO oracle's ∀P' ranges over 2**(n**arity) relations per structure, on
#: top of enumerating every structure up to this size).
BOUND = 3


def _agree(premises, circumscribed, conclusion, expected, max_size=BOUND):
    """Assert both oracles agree with ``expected`` (the hand-derived verdict)."""
    me = minimal_entails(premises, conclusion, circumscribed, max_size=max_size)
    axiom = circumscription_entails_so(premises, circumscribed, conclusion)
    so = so_is_valid_finite(axiom, max_size=max_size)
    assert me == expected, f"minimal_entails: got {me}, expected {expected}"
    assert so == expected, f"so_is_valid_finite(circumscription_entails_so(...)): got {so}, expected {expected}"
    assert me == so
    return axiom


# ---------------------------------------------------------------------------
# The classic bird/penguin abnormality pattern, circumscribing Ab with Bird /
# Penguin FIXED (the "simple all-others-fixed" reading this builder
# implements — see circumscription_formula's docstring). The conclusions are
# stated directly about Ab (NOT a further "Flies" predicate *defined* from Ab
# by a biconditional): a FIXED predicate is compared as a rigid parameter
# across models, so deriving one from the circumscribed predicate via a
# defining formula and then asking about ITS minimal value is a DIFFERENT
# (more advanced, "let Flies vary") reading this builder does not implement —
# confirmed empirically: adding a `Flies ↔ (Bird ∧ ¬Ab)` premise and asking
# for minimal-Flies(tweety) makes BOTH oracles agree on False (there is a
# consistent — if perverse — fixed choice Flies(tweety)=False forcing
# Ab(tweety)=True, and that choice is trivially "minimal" within its own
# fixed-part group), which is correct under all-fixed semantics even though
# it is not the naive expectation. Asking about Ab directly sidesteps this.
# ---------------------------------------------------------------------------

_X = Variable("x")
TWEETY, OPUS = Constant("tweety"), Constant("opus")

_PENGUIN_BIRD = Quantifier("∀", _X, Implies(Atom("Penguin", (_X,)), Atom("Bird", (_X,))))
_PENGUIN_AB = Quantifier("∀", _X, Implies(Atom("Penguin", (_X,)), Atom("Ab", (_X,))))
_BIRD_TWEETY = Atom("Bird", (TWEETY,))
_NOT_PENGUIN_TWEETY = Not(Atom("Penguin", (TWEETY,)))

_BASE_PREMISES = [_PENGUIN_BIRD, _PENGUIN_AB, _BIRD_TWEETY, _NOT_PENGUIN_TWEETY]


class TestBirdPenguin:
    def test_non_penguin_bird_is_not_abnormal(self):
        # Ab is circumscribed (minimised); nothing in the premises forces
        # Ab(tweety) (Penguin(tweety) is explicitly FALSE, so the
        # Penguin->Ab premise never fires for tweety, and no other premise
        # mentions Ab) -> every minimal model has Ab(tweety) = False.
        _agree(_BASE_PREMISES, {"Ab"}, Not(Atom("Ab", (TWEETY,))), expected=True)

    def test_penguin_is_abnormal(self):
        # Add Penguin(opus): Ab(opus) is then FORCED TRUE in EVERY model (not
        # just minimal ones) by the Penguin->Ab premise -- true regardless of
        # minimisation, hence in particular in every minimal model.
        premises = _BASE_PREMISES + [Atom("Penguin", (OPUS,))]
        _agree(premises, {"Ab"}, Atom("Ab", (OPUS,)), expected=True)

    def test_non_penguin_bird_is_not_entailed_abnormal_the_other_way(self):
        # The negation of the first case: Ab(tweety) must NOT be
        # (circumscriptively) entailed, since every minimal model in fact has
        # Ab(tweety) = False.
        _agree(_BASE_PREMISES, {"Ab"}, Atom("Ab", (TWEETY,)), expected=False)


# ---------------------------------------------------------------------------
# Minimal-extension shape facts (McCarthy's original motivating examples).
# ---------------------------------------------------------------------------

class TestMinimalExtensionShape:
    def test_empty_premises_circumscribe_to_the_empty_extension(self):
        # No premises at all -> nothing forces ANY element into P -> the
        # (unique, up to the fixed part) minimal extension is EMPTY, so ¬P(b)
        # holds in every minimal model for ANY b. Arity of P is inferable only
        # from the conclusion here (empty premises), which
        # circumscription_entails_so handles (unlike circumscription_formula
        # alone -- see test_arity_from_conclusion_only below).
        _agree([], {"P"}, Not(Atom("P", (Constant("b"),))), expected=True)

    def test_single_fact_circumscribes_to_exactly_that_element(self):
        # P(a) alone: minimality forces P to be the SMALLEST set containing a,
        # i.e. exactly {a} -- so "everything in P equals a" holds in every
        # minimal model.
        premises = [Atom("P", (Constant("a"),))]
        conclusion = Quantifier("∀", _X, Implies(Atom("P", (_X,)), Atom("=", (_X, Constant("a")))))
        _agree(premises, {"P"}, conclusion, expected=True)

    def test_single_fact_does_not_force_a_second_unrelated_element_out(self):
        # Sanity dual of the above: P(a) alone does NOT entail ¬P(a) itself
        # (P(a) trivially holds in the minimal model P={a}).
        premises = [Atom("P", (Constant("a"),))]
        _agree(premises, {"P"}, Atom("P", (Constant("a"),)), expected=True)

    def test_disjunctive_fact_never_forces_both_disjuncts_into_a_minimal_model(self):
        # P(a) ∨ P(b), with a ≠ b asserted explicitly (so the two constants
        # cannot coincide and blur the case analysis): the minimal models are
        # exactly those with P = {a} or P = {b} (P = {a,b} satisfies the
        # premise but is NOT minimal, since {a} ⊊ {a,b} already satisfies it)
        # -- so P(a) ∧ P(b) never holds in a minimal model.
        premises = [Or(Atom("P", (Constant("a"),)), Atom("P", (Constant("b"),))),
                   Not(Atom("=", (Constant("a"), Constant("b"))))]
        conclusion = Not(And(Atom("P", (Constant("a"),)), Atom("P", (Constant("b"),))))
        _agree(premises, {"P"}, conclusion, expected=True)


# ---------------------------------------------------------------------------
# Multiple circumscribed predicates, and the "everything else fixed" reading.
# ---------------------------------------------------------------------------

class TestMultiplePredicatesAndFixedness:
    def test_jointly_circumscribing_two_independent_predicates(self):
        # P(a), Q(b): circumscribing {P, Q} TOGETHER minimises each
        # independently when the premises don't couple them (no formula
        # mentions both) -- minimal models have P={a}, Q={b} exactly, so
        # b ∉ P (and a ∉ Q) in every minimal model.
        premises = [Atom("P", (Constant("a"),)), Atom("Q", (Constant("b"),)),
                   Not(Atom("=", (Constant("a"), Constant("b"))))]
        conclusion = Not(Atom("P", (Constant("b"),)))
        _agree(premises, {"P", "Q"}, conclusion, expected=True)

    def test_a_non_circumscribed_predicate_is_fixed_not_forced_empty(self):
        # R is NOT circumscribed (only P is): R(c) is an outright fact, so it
        # holds in EVERY model of the premises, hence in every minimal model
        # too -- fixed does not mean "minimised to empty", it means "not
        # compared for minimality" (R keeps whatever value the premises give
        # it in each model).
        premises = [Atom("P", (Constant("a"),)), Atom("R", (Constant("c"),))]
        _agree(premises, {"P"}, Atom("R", (Constant("c"),)), expected=True)


# ---------------------------------------------------------------------------
# circumscription_formula / circumscription_entails_so: interface behaviour
# (not just the differential — structural facts about the builder itself).
# ---------------------------------------------------------------------------

class TestBuilderInterface:
    def test_bare_name_and_explicit_arity_tuple_give_the_same_verdict(self):
        # Same predicate spec, two spellings: circumscribed={"P"} (arity
        # inferred from the premises) vs {("P", 1)} (explicit) must decide the
        # SAME question the same way.
        premises = [Atom("P", (Constant("a"),))]
        conclusion = Not(Atom("P", (Constant("b"),)))
        me_bare = minimal_entails(premises, conclusion, {"P"}, max_size=BOUND)
        me_tuple = minimal_entails(premises, conclusion, {"P"}, max_size=BOUND)  # same call, sanity
        axiom_bare = circumscription_entails_so(premises, {"P"}, conclusion)
        axiom_tuple = circumscription_entails_so(premises, {("P", 1)}, conclusion)
        so_bare = so_is_valid_finite(axiom_bare, max_size=BOUND)
        so_tuple = so_is_valid_finite(axiom_tuple, max_size=BOUND)
        assert me_bare == me_tuple == so_bare == so_tuple

    def test_arity_from_conclusion_only(self):
        # circumscription_formula alone cannot infer P's arity from EMPTY
        # premises; circumscription_entails_so can, because it also scans the
        # conclusion.
        try:
            circumscription_formula([], {"P"})
        except ValueError as e:
            assert "cannot infer the arity" in str(e)
        else:
            raise AssertionError("expected ValueError for an unresolvable bare-name arity")
        # But circumscription_entails_so succeeds (arity 1, from ¬P(b)).
        axiom = circumscription_entails_so([], {"P"}, Not(Atom("P", (Constant("b"),))))
        assert isinstance(axiom, Implies)

    def test_explicit_arity_tuple_bypasses_inference_even_with_premises(self):
        # An explicit (name, arity) pair is honoured even when premises alone
        # WOULD have determined a (consistent) arity -- no error, no override.
        f = circumscription_formula([Atom("P", (Constant("a"),))], {("P", 1)})
        assert isinstance(f, And)

    def test_varied_not_implemented(self):
        try:
            circumscription_formula([Atom("P", (Constant("a"),))], {"P"}, varied=("Q",))
        except NotImplementedError as e:
            assert "varied" in str(e)
        else:
            raise AssertionError("expected NotImplementedError for a non-empty `varied`")

    def test_empty_circumscribed_set_rejected(self):
        try:
            circumscription_formula([Atom("P", (Constant("a"),))], set())
        except ValueError as e:
            assert "at least one predicate" in str(e)
        else:
            raise AssertionError("expected ValueError for an empty `circumscribed`")

    def test_conflicting_arity_in_premises_rejected(self):
        # P used at arity 1 in one premise and arity 2 in another -- an
        # ill-formed signature for a single circumscribed predicate name.
        premises = [Atom("P", (Constant("a"),)),
                   Atom("P", (Constant("a"), Constant("b")))]
        try:
            circumscription_formula(premises, {"P"})
        except ValueError as e:
            assert "conflicting arities" in str(e)
        else:
            raise AssertionError("expected ValueError for conflicting P arities")

    def test_degenerate_empty_premises_has_no_leading_conjunct(self):
        # With premises=[], T(P) is vacuously true and is dropped rather than
        # wrapped as `True ∧ …` -- the formula is exactly the ∀P'(...) axiom,
        # a bare SecondOrderQuantifier (not an And).
        axiom = circumscription_formula([], {("P", 1)})
        assert isinstance(axiom, SecondOrderQuantifier)

    def test_non_empty_premises_wraps_with_the_conjunct(self):
        axiom = circumscription_formula([Atom("P", (Constant("a"),))], {"P"})
        assert isinstance(axiom, And)

    def test_circumscription_entails_so_returns_an_implication(self):
        f = circumscription_entails_so(
            [Atom("P", (Constant("a"),))], {"P"}, Atom("P", (Constant("a"),)))
        assert isinstance(f, Implies)
