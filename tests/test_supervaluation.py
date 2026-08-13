"""Tests for policy="supervaluation" on free_satisfies (semantics/free_logic.py).

Every expected verdict is hand-derived in a comment. Supervaluationism treats a
ground atom with a non-denoting term as a genuine truth-value GAP rather than
forcing it false (as the "negative" policy does): a *precisification* completes
every gap atom to True or False, consistently for that ground atom wherever it
recurs, and the formula is

- supertrue  (reported as True)  iff EVERY precisification makes it True,
- superfalse (reported as False) iff EVERY precisification makes it False,
- a gap      (reported as False) otherwise -- since free_satisfies always returns
  a plain bool, a genuine gap collapses to the same False a lone gappy atom
  already returns under "negative"; the tests below distinguish "gap" from
  "superfalse" by also checking the negation, which is supertrue exactly when
  the original was superfalse, but ALSO a gap (False) when the original was
  itself a gap (a gap's negation is a gap too, since it has the same set of
  disagreeing precisifications with True/False swapped).

The defining phenomenon supervaluationism is built for: classical tautologies
survive even though their DISJUNCTS, evaluated individually, are themselves
gaps. That is the running example, `P(e) ∨ ¬P(e)` for non-denoting `e`, checked
by `test_excluded_middle_is_supertrue_though_each_disjunct_is_a_gap`.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Quantifier, Variable, Constant,
)
from unicode_fol_kit.semantics.free_logic import (
    FreeModel, free_satisfies, free_holds,
    free_is_valid, free_entails, free_find_model, free_countermodel,
    SUPERVALUATION_MAX_GAPS,
)


x = Variable("x")
e = Constant("e")          # non-denoting in every model below unless stated otherwise
a = Constant("a")          # denoting, where used
Px = lambda t: Atom("P", [t])
Qx = lambda t: Atom("Q", [t])


def _model(existing=(0,), p_true=(), q_true=(), constants=None):
    """A one-object-outer FreeModel (outer domain {0}); `e`/`a` denote per `constants`."""
    return FreeModel(
        outer=(0,),
        existing=frozenset(existing),
        constants=constants or {},
        predicates={
            ("P", 1): frozenset((v,) for v in p_true),
            ("Q", 1): frozenset((v,) for v in q_true),
        },
    )


# --------------------------------------------------------------------------- #
# The excluded-middle contrast: the paradigm case for supervaluationism.
# --------------------------------------------------------------------------- #

def test_excluded_middle_is_supertrue_though_each_disjunct_is_a_gap():
    # e is absent from `constants`, so P(e) has a non-denoting argument: it is a
    # gap atom. Under precisification P(e)=True, P(e) is true, so P(e) alone is
    # NOT supertrue (some precisification makes it false); under P(e)=False, it
    # is false, so P(e) alone is NOT superfalse either (some precisification
    # makes it true). Hence P(e) alone is a genuine gap -> reported False.
    m = _model()
    assert free_satisfies(Px(e), m, {}, "supervaluation") is False
    # Same reasoning, precisifications swapped: ¬P(e) is also a gap -> False.
    assert free_satisfies(Not(Px(e)), m, {}, "supervaluation") is False

    # But P(e) ∨ ¬P(e): under EITHER precisification of P(e), one disjunct is
    # true (True∨False=True, or False∨True=True) -- so BOTH of the two possible
    # precisifications make the whole disjunction true: it is supertrue, unlike
    # naively OR-ing each disjunct's own (gappy -> False) supervaluation verdict,
    # which would wrongly suggest False∨False=False.
    excluded_middle = Or(Px(e), Not(Px(e)))
    assert free_satisfies(excluded_middle, m, {}, "supervaluation") is True
    # Contrast with "negative": there every atom with a non-denoting term is
    # forced false outright (no genuine gap machinery), so P(e)=False already,
    # and P(e)∨¬P(e) = False∨True = True too -- "negative" reaches the SAME
    # verdict on the whole disjunction here, but for a fundamentally different
    # reason (no gap ever arose), which is exactly why P(e) alone already
    # differs: "negative" reports Px(e) as a flat False (a decided falsehood),
    # while supervaluation reports it False only as a stand-in for "gap".
    assert free_satisfies(Px(e), m, {}, "negative") is False
    assert free_satisfies(excluded_middle, m, {}, "negative") is True


def test_bare_gap_atom_alone_is_reported_false_not_supertrue():
    # P(e) by itself: reported False (the gap convention), and definitely NOT
    # reported True -- confirms supervaluation does not just default-true a gap.
    m = _model()
    assert free_satisfies(Px(e), m, {}, "supervaluation") is False


# --------------------------------------------------------------------------- #
# Superfalse: a contradiction is false under EVERY precisification.
# --------------------------------------------------------------------------- #

def test_contradiction_is_superfalse():
    # P(e) ∧ ¬P(e): under precisification True, True∧False=False; under False,
    # False∧True=False. Both precisifications agree on False -> superfalse.
    m = _model()
    contradiction = And(Px(e), Not(Px(e)))
    assert free_satisfies(contradiction, m, {}, "supervaluation") is False
    # Its negation, ¬(P(e) ∧ ¬P(e)), is then supertrue (the De Morgan dual of
    # excluded middle) -- this is what actually certifies "superfalse" rather
    # than "gap" for the contradiction itself, since both report False raw.
    assert free_satisfies(Not(contradiction), m, {}, "supervaluation") is True


# --------------------------------------------------------------------------- #
# Supertrue via a denoting disjunct: the gap does not have to be resolved when
# the OTHER disjunct already settles the formula under every precisification.
# --------------------------------------------------------------------------- #

def test_disjunction_with_a_true_denoting_disjunct_is_supertrue():
    # a denotes 0, and Q(0) is true, so Q(a) is true outright (not gappy) under
    # every precisification of the unrelated gap atom P(e). Hence P(e) ∨ Q(a)
    # is true under both precisifications of P(e) -> supertrue.
    m = _model(q_true=(0,), constants={"a": 0})
    formula = Or(Px(e), Qx(a))
    assert free_holds(Qx(a), m, policy="supervaluation") is True   # sanity: Q(a) itself is decided
    assert free_holds(formula, m, policy="supervaluation") is True


# --------------------------------------------------------------------------- #
# Quantifiers are unaffected: ∃/∀ range only over model.existing, exactly as
# under the other two policies -- supervaluation only ever touches non-denoting
# GROUND atoms, never the domain quantifiers range over.
# --------------------------------------------------------------------------- #

def test_quantifiers_still_range_only_over_the_existing_domain():
    # existing = {0}; e is non-denoting and plays no role in ∃x P(x) at all,
    # since x is bound and only ever takes the value 0 (the sole existing
    # object), never NONDENOTING. So this formula has NO gap atoms, and
    # supervaluation must agree with every other policy (a single, trivial,
    # "precisification" over zero gaps).
    m = _model(existing=(0,), p_true=())   # P is empty on {0}
    exists_p = Quantifier("∃", x, Px(x))
    assert free_satisfies(exists_p, m, {}, "supervaluation") is False
    assert free_satisfies(exists_p, m, {}, "negative") is False
    assert free_satisfies(exists_p, m, {}, "positive") is False

    m2 = _model(existing=(0,), p_true=(0,))   # P(0) holds
    assert free_satisfies(exists_p, m2, {}, "supervaluation") is True
    assert free_satisfies(exists_p, m2, {}, "negative") is True

    forall_p = Quantifier("∀", x, Px(x))
    assert free_satisfies(forall_p, m2, {}, "supervaluation") is True


# --------------------------------------------------------------------------- #
# Two independent gap atoms interacting: the value depends on which of the 4
# precisifications is taken, and they do not all agree -> a gap.
# --------------------------------------------------------------------------- #

def test_two_gap_atoms_interacting_stays_a_gap():
    # P(e) and Q(e) are both non-denoting (same non-denoting argument e, but
    # DIFFERENT predicates -- two distinct gap atoms, precisified independently).
    # Formula: P(e) ∨ ¬Q(e). By hand, over (P,Q) in {T,F}x{T,F}:
    #   P=T,Q=T: T ∨ ¬T = T ∨ F = T
    #   P=T,Q=F: T ∨ ¬F = T ∨ T = T
    #   P=F,Q=T: F ∨ ¬T = F ∨ F = F
    #   P=F,Q=F: F ∨ ¬F = F ∨ T = T
    # Not all 4 agree (one is False, three are True) -> not supertrue, not
    # superfalse -> a genuine gap -> reported False.
    m = _model()
    formula = Or(Px(e), Not(Qx(e)))
    assert free_satisfies(formula, m, {}, "supervaluation") is False
    # Confirm it is a genuine gap, not superfalse: the negation is ALSO not
    # supertrue (superfalse's negation would be supertrue; a gap's negation
    # stays a gap, i.e. also reported False), since negating swaps T/F on the
    # very same 4 rows, and they still disagree (three False, one True).
    assert free_satisfies(Not(formula), m, {}, "supervaluation") is False


def test_two_gap_atoms_where_all_four_precisifications_agree_is_supertrue():
    # P(e) ∨ Q(e) ∨ ¬P(e): whatever P(e) is precisified to, either P(e) or
    # ¬P(e) is true, regardless of Q(e) -- so all 4 precisifications give True.
    m = _model()
    formula = Or(Or(Px(e), Qx(e)), Not(Px(e)))
    assert free_satisfies(formula, m, {}, "supervaluation") is True


# --------------------------------------------------------------------------- #
# free_is_valid / free_entails / free_find_model / free_countermodel thread
# policy="supervaluation" through exactly like "negative" / "positive".
# --------------------------------------------------------------------------- #

def test_search_functions_accept_the_supervaluation_policy():
    # Excluded middle is a free-logic-wide validity under supervaluation: no
    # FreeModel at any bounded size can make P(x) ∨ ¬P(x) fail, because for
    # ANY x (bound, so never non-denoting) it is a plain classical tautology,
    # and for any constant substituted in, the argument above (both
    # precisifications agree True) applies regardless of which model is tried.
    tautology = Or(Px(e), Not(Px(e)))
    assert free_is_valid(tautology, policy="supervaluation") is True
    assert free_countermodel(tautology, policy="supervaluation") is None

    # A satisfiable-but-not-valid formula: free_find_model should locate a
    # witnessing model under supervaluation just like under the other policies.
    witness = free_find_model(Qx(a), policy="supervaluation", max_size=2)
    assert witness is not None
    assert free_satisfies(Qx(a), witness, {}, "supervaluation") is True

    # free_entails threads the policy too: {P(e)} does not supervaluation-
    # entail Q(e) in general (no relation asserted between the two predicates).
    assert free_entails([Px(e)], Qx(e), policy="supervaluation", max_size=2) is False


# --------------------------------------------------------------------------- #
# The hard cap on distinct gap atoms.
# --------------------------------------------------------------------------- #

def test_too_many_gap_atoms_raises_rather_than_silently_truncating():
    # Build a formula with SUPERVALUATION_MAX_GAPS + 1 distinct gap atoms: one
    # differently-named non-denoting constant per gap atom, each wrapped in its
    # own (distinct) unary predicate so they cannot collapse into fewer keys.
    m = _model()
    n = SUPERVALUATION_MAX_GAPS + 1
    atoms = [Atom(f"R{i}", [Constant(f"g{i}")]) for i in range(n)]
    formula = atoms[0]
    for atom in atoms[1:]:
        formula = Or(formula, atom)
    with pytest.raises(ValueError, match="SUPERVALUATION_MAX_GAPS"):
        free_satisfies(formula, m, {}, "supervaluation")


def test_exactly_at_the_cap_does_not_raise():
    # SUPERVALUATION_MAX_GAPS distinct gap atoms is still within bounds: 2**16
    # precisifications is large but finite, and the function should complete
    # (all disjuncts are gap atoms with no way to force a value, so the
    # disjunction of that many independent gaps is supertrue: some
    # precisification makes at least one True in EVERY completion except the
    # all-False one, but the all-False completion exists too -> genuinely a
    # gap here, not supertrue; the point of this test is only that it does not
    # raise, not what the exact verdict is).
    m = _model()
    n = SUPERVALUATION_MAX_GAPS
    atoms = [Atom(f"S{i}", [Constant(f"h{i}")]) for i in range(n)]
    formula = atoms[0]
    for atom in atoms[1:]:
        formula = Or(formula, atom)
    result = free_satisfies(formula, m, {}, "supervaluation")
    assert result is False   # the all-False precisification exists -> not supertrue -> gap


# --------------------------------------------------------------------------- #
# Unknown-policy rejection still fires (mirrors the pre-existing negative/
# positive check; "supervaluation" itself is of course now accepted).
# --------------------------------------------------------------------------- #

def test_unknown_policy_still_raises():
    m = _model()
    with pytest.raises(ValueError, match="unknown policy"):
        free_satisfies(Px(e), m, {}, "made_up_policy")
    with pytest.raises(ValueError, match="unknown policy"):
        free_is_valid(Px(e), policy="made_up_policy")
