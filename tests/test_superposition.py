"""Tests for equality reasoning in the resolution prover — Tier 3
"Resolution-Superposition, abgestuft": paramodulation, reflexivity
resolution, and demodulation added to :mod:`unicode_fol_kit.atp.resolution`,
plus the matching three new rule kinds
(``"paramodulate"``/``"reflexivity"``/``"demodulate"``)
independently re-verified by :mod:`unicode_fol_kit.atp.resolution_check`.
A shared-instance ``self_paramodulate`` shortcut existed briefly and was
REMOVED as unsound by the Tier-3 adversarial review (for ``{u ≈ v, L[u]}``
it inferred ``{L[v]}``, false in a model satisfying the clause via ``L[u]``
alone with ``u ≠ v``) — the regression tests below pin both the prover
no longer deriving through it and the checker rejecting the rule name.

Before this change, ``"="`` was — and, on its own, still is — an ORDINARY
uninterpreted binary predicate to every existing mechanism in this module: no
reflexivity/symmetry/transitivity/congruence axioms were ever injected
anywhere in the resolution pipeline, and none are injected now either.
``prove([Atom("=",[a,b])], Atom("=",[Function("f",[a]), Function("f",[b])]))``
returned False before this change (confirmed by running it against the
unmodified module) and returns True now, purely because paramodulation adds
equality's INFERENCE RULES, not because any axiom was added anywhere.

Every expected value below is hand-derived (see the comment above each
assertion) and, for the internal generator functions, additionally confirmed
by direct interpreter output before being written down — the same "hand
derivation, not test-first-blind" discipline test_resolution.py,
test_resolution_check.py, and test_resolution_redundancy.py already use.

Sections:
  1. The term order (_term_weight / _term_gt / _paramodulation_directions).
  2. Subterm positions (_subterm_positions / _term_at / _replace_at).
  3. The equality generators (_paramodulants_cross /
     _reflexivity_resolvents) and demodulation
     (_unit_rewrite_rules / _demodulate_once / _demodulate_to_fixpoint),
     plus the self-paramodulation unsoundness regressions.
  4. End-to-end provability: (a) congruence, (b) transitivity+symmetry,
     (c) paramodulation into a predicate, (d) a goal needing a universally
     quantified equation, (e) reflexivity (two flavours), (f) a small group-
     theory lemma, (g) a NEGATIVE (non-entailment) soundness guard.
  5. Round trips: hand-built ResolutionDerivation certificates for several of
     the proofs above (and a standalone one for demodulate,
     which the end-to-end examples above don't happen to need), each checked
     by verify_resolution_proof.
  6. TAMPER cases (>=6): a manipulated step must be rejected with a precise
     error, covering all three new rule kinds.
  7. A differential check that resolution.py's and resolution_check.py's
     independently reimplemented term orders agree — the same independence
     discipline test_resolution_check.py's unification battery already uses.

Regression protection for the surrounding module lives in test_resolution.py,
test_resolution_check.py, and test_resolution_redundancy.py; all three stay
green (run alongside this file) since no existing behaviour changes for
equality-free clause sets — the new generators immediately return ``[]`` the
moment a clause has no "=" literal to work with, costing zero extra steps.
"""

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Variable, Constant, Function, Quantifier,
)
from unicode_fol_kit.atp.resolution import (
    prove, is_valid_resolution, refute,
    _term_weight, _term_gt, _paramodulation_directions,
    _subterm_positions, _term_at, _replace_at,
    _paramodulants_cross, _reflexivity_resolvents,
    _unit_rewrite_rules, _demodulate_once, _demodulate_to_fixpoint,
)
from unicode_fol_kit.atp.resolution_check import (
    ResolutionStep, ResolutionDerivation, verify_resolution_proof,
    render_resolution_proof,
    _term_gt as _check_term_gt,
)


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


def EQ(s, t):
    return Atom("=", [s, t])


x, y = Variable("x"), Variable("y")
a, b, c = Constant("a"), Constant("b"), Constant("c")


def f(t):
    return Function("f", [t])


def g(t):
    return Function("g", [t])


# ---------------------------------------------------------------------------
# 1. The term order: weight = term size, ties lexicographic by
#    to_unicode_str(). See _term_gt's docstring for the full definition and
#    why no substitution-compatibility closure is needed.
# ---------------------------------------------------------------------------

def test_term_weight_leaves_are_one():
    assert _term_weight(a) == 1
    assert _term_weight(x) == 1  # a Variable is a leaf too


def test_term_weight_function_is_one_plus_children():
    # f(a): 1 (for f) + 1 (for a) = 2.
    assert _term_weight(f(a)) == 2
    # f(f(a)): 1 + weight(f(a)) = 1 + 2 = 3.
    assert _term_weight(f(f(a))) == 3
    # g(a,b) (binary): 1 + 1 + 1 = 3.
    assert _term_weight(Function("g", [a, b])) == 3


def test_term_gt_by_weight():
    # f(a) has weight 2, a has weight 1: f(a) is strictly heavier.
    assert _term_gt(f(a), a) is True
    assert _term_gt(a, f(a)) is False


def test_term_gt_tie_broken_lexicographically():
    # a and b both weigh 1 (leaves); "a" < "b" as strings (to_unicode_str()
    # renders each as its bare name), so b is the order-greater side.
    assert _term_gt(b, a) is True
    assert _term_gt(a, b) is False
    # f(x) and g(x) both weigh 2 (1 + 1 for the shared leaf argument);
    # "f(x)" < "g(x)" lexicographically ('f' < 'g'), so g(x) is greater.
    assert _term_gt(g(x), f(x)) is True
    assert _term_gt(f(x), g(x)) is False


def test_term_gt_irreflexive():
    # A term is never strictly greater than itself (same weight, same
    # rendering) — confirms "incomparable" under this order collapses to
    # genuine term equality, as the module docstring states.
    assert _term_gt(a, a) is False
    assert _term_gt(f(x), f(x)) is False


def test_paramodulation_directions_strict_case():
    # b > a strictly, so only the (b -> a) direction is licensed.
    assert _paramodulation_directions(b, a) == [(b, a)]
    assert _paramodulation_directions(a, b) == [(b, a)]


def test_paramodulation_directions_incomparable_tries_both():
    # u and v identical (a, a): the order does not strictly decide (a is not
    # > a), so both (a,a) and (a,a) directions are offered — harmless (both
    # are the same no-op rewrite), but confirms the fallback path fires
    # exactly where the module docstring says it should.
    dirs = _paramodulation_directions(a, a)
    assert dirs == [(a, a), (a, a)]


# ---------------------------------------------------------------------------
# 2. Subterm positions, extraction, and replacement.
# ---------------------------------------------------------------------------

def test_subterm_positions_pinned():
    # P(f(a), b): position (0,) is f(a) itself, (0,0) is its argument a,
    # (1,) is b. Pre-order, left to right; no position is yielded for a bare
    # Variable (none occurs here).
    atom = P(f(a), b)
    assert list(_subterm_positions(atom)) == [(0,), (0, 0), (1,)]


def test_subterm_positions_excludes_variables():
    # P(x, f(x)): the bare-variable argument at index 0 yields NO position
    # (paramodulating into a variable occurrence is deliberately excluded —
    # see _subterm_positions' docstring); f(x) at (1,) and its argument x at
    # (1,0) do not exist as separate variable positions either, so only
    # (1,) is yielded.
    atom = P(x, f(x))
    assert list(_subterm_positions(atom)) == [(1,)]


def test_term_at_and_replace_at_roundtrip():
    atom = P(f(a), b)
    assert _term_at(atom, (0,)) == f(a)
    assert _term_at(atom, (0, 0)) == a
    assert _term_at(atom, (1,)) == b
    # Replacing (0,0) [the 'a' inside f(a)] with c gives P(f(c), b).
    assert _replace_at(atom, (0, 0), c) == P(f(c), b)
    # Replacing the whole (0,) subterm [f(a)] with c gives P(c, b).
    assert _replace_at(atom, (0,), c) == P(c, b)


# ---------------------------------------------------------------------------
# 3. The equality generators (mirroring how test_resolution_redundancy.py
#    unit-tests _match/_subsumes directly, not only through refute()).
# ---------------------------------------------------------------------------

def test_paramodulants_cross_pinned():
    # eq_clause {a=b}: only direction (b -> a) is licensed (b > a). Target
    # clause {P(b), Q(a)}: 'b' occurs inside P(b) at position (0,), matching
    # trivially (sigma={}); Q(a) has no 'b' anywhere. The paramodulant is
    # (eq_clause \ {a=b}) [empty, unit clause] union (target \ {P(b)})
    # [{Q(a)}] union {P(a)} [the rewritten literal] = {P(a), Q(a)}.
    eq_clause = frozenset({EQ(a, b)})
    target_clause = frozenset({P(b), Q(a)})
    results = _paramodulants_cross(eq_clause, target_clause)
    assert len(results) == 1
    assert results[0] == frozenset({P(a), Q(a)})


def test_paramodulants_cross_empty_without_a_positive_equality_literal():
    # Neither clause carries a positive "=" literal, so nothing can license
    # a rewrite — confirms the cheap early-exit that keeps equality-free
    # regression tests unaffected (see the module docstring).
    c1 = frozenset({P(a)})
    c2 = frozenset({Q(a)})
    assert _paramodulants_cross(c1, c2) == []
    assert _paramodulants_cross(c2, c1) == []


def test_self_paramodulation_unsound_shortcut_is_gone():
    """The removed shared-instance shortcut would have "proved" this
    NON-entailment (adversarial-review soundness regression).

    Hand derivation of the false proof the shortcut licensed:
    {a=b, ¬P(b)} self-paramodulating (b→a into its own ¬P(b), both consumed
    literals dropped) yielded {¬P(a)}, which resolves with {P(a)} to the
    empty clause. But the set { a=b ∨ ¬P(b), P(a) } is SATISFIABLE — model:
    a≠b, P(b)=false (first clause true via ¬P(b)), P(a)=true — so refute()
    must saturate without the empty clause. The sound cross path derives
    only the weaker {¬P(b'), a=b', ¬P(a)}-shaped paramodulants, which never
    close against {P(a)} alone.
    """
    clauses = {frozenset({EQ(a, b), Not(P(b))}), frozenset({P(a)})}
    assert refute(clauses) is False


def test_prover_module_has_no_self_paramodulation_generator():
    """The unsound generator is gone from the module surface, not just
    unplugged — importing it must fail (pins the removal itself)."""
    import unicode_fol_kit.atp.resolution as resolution
    assert not hasattr(resolution, "_paramodulants_self")


def test_reflexivity_resolvents_pinned():
    # {~(x=x), P(a)}: u=v=x unify trivially (sigma={}); dropping the literal
    # leaves {P(a)}.
    clause = frozenset({Not(EQ(x, x)), P(a)})
    assert _reflexivity_resolvents(clause) == [frozenset({P(a)})]


def test_reflexivity_resolvents_needs_unifiable_sides():
    # {~(a=c)}: a and c are distinct constants — no unifier, no resolvent.
    assert _reflexivity_resolvents(frozenset({Not(EQ(a, c))})) == []


def test_unit_rewrite_rules_orients_by_the_term_order():
    # {f(x)=a}: weight(f(x))=2 > weight(a)=1, so the rule is oriented
    # f(x) -> a (not the reverse).
    rule_clause = frozenset({EQ(f(x), a)})
    rules = _unit_rewrite_rules([rule_clause])
    assert rules == [(f(x), a)]


def test_unit_rewrite_rules_skips_non_unit_clauses():
    # {a=b, Q(c)} only asserts a=b OR Q(c) — never usable as an
    # unconditional rewrite rule.
    non_unit = frozenset({EQ(a, b), Q(c)})
    assert _unit_rewrite_rules([non_unit]) == []


def test_demodulate_once_and_fixpoint_pinned():
    # Rule f(x) -> a (from {f(x)=a}); target {P(f(b)), P(c)}. The 'f(b)'
    # subterm of P(f(b)) matches f(x) with x:=b (one-sided match, own
    # _match_term), giving rSIGMA = a; P(c) has nothing to rewrite.
    rules = _unit_rewrite_rules([frozenset({EQ(f(x), a)})])
    target = frozenset({P(f(b)), P(c)})
    once = _demodulate_once(target, rules)
    assert once == frozenset({P(a), P(c)})
    # A second pass finds nothing left to rewrite: the fixpoint is reached
    # after exactly 1 rewrite.
    fixed, count = _demodulate_to_fixpoint(target, rules)
    assert count == 1
    assert fixed == frozenset({P(a), P(c)})


def test_demodulate_once_none_when_no_rule_matches():
    rules = _unit_rewrite_rules([frozenset({EQ(f(x), a)})])
    assert _demodulate_once(frozenset({P(c)}), rules) is None
    fixed, count = _demodulate_to_fixpoint(frozenset({P(c)}), rules)
    assert count == 0
    assert fixed == frozenset({P(c)})


# ---------------------------------------------------------------------------
# 4. End-to-end provability.
# ---------------------------------------------------------------------------

# --- (a) Congruence: {a=b} |= f(a)=f(b) ---
#
# Hand derivation: negate the goal -> {~(f(a)=f(b))}. b > a (weight tie,
# lexical), so paramodulating {a=b} only licenses (b -> a). The subterm 'b'
# inside f(b) (position (1,0) of the negated goal's atom) matches trivially;
# rewriting gives ~(f(a)=f(a)). Reflexivity resolution (f(a) unifies with
# itself) then empties the clause.

def test_congruence_provable():
    assert prove([EQ(a, b)], EQ(f(a), f(b)), max_steps=2000) is True


# --- (b) Transitivity + symmetry chain: {a=b, b=c} |= c=a ---
#
# a < b < c lexically (all weight 1), so {a=b} orients (b->a) and {b=c}
# orients (c->b). Negated goal {~(c=a)}: paramodulating (c->b) rewrites the
# 'c' at position (0,) to give ~(b=a); paramodulating (b->a) then rewrites
# the 'b' at position (0,) to give ~(a=a); reflexivity closes it. Note the
# goal is written "c=a" (not "a=c") specifically to exercise SYMMETRY too —
# paramodulation finds subterms wherever they occur structurally, not just
# on a conventional "left" side of "=", so no separate symmetry axiom/rule
# is needed for this to work.

def test_transitivity_and_symmetry_chain_provable():
    assert prove([EQ(a, b), EQ(b, c)], EQ(c, a), max_steps=2000) is True


# --- (c) Paramodulation into a predicate: {a=b, P(a)} |= P(b) ---
#
# Negated goal {~P(b)}: paramodulating {a=b} (direction b->a, the only one
# licensed) rewrites the 'b' argument of ~P(b) to 'a', giving ~P(a), which
# then resolves directly (ordinary binary resolution) against {P(a)}.

def test_paramodulation_into_predicate_provable():
    assert prove([EQ(a, b), P(a)], P(b), max_steps=2000) is True


# --- (d) A goal needing a universally quantified equation: ---
#     {forall x (f(x)=g(x)), P(f(c))} |= P(g(c))
#
# g(x) and f(x) tie in weight (2 each); "f(x)" < "g(x)" lexically, so g(x) is
# the order-greater side and only (g(x) -> f(x)) is licensed. Negated goal
# {~P(g(c))}: the subterm g(c) at position (0,) unifies with g(x) via
# x:=c, rewriting to ~P(f(c)) — which resolves directly against P(f(c)).

def test_goal_needs_universally_quantified_equation():
    premise = Quantifier("forall", x, EQ(f(x), g(x)))
    assert prove([premise, P(f(c))], P(g(c)), max_steps=2000) is True


# --- (e) Reflexivity ---

def test_reflexivity_goal_c_equals_c():
    # |= c=c: negated, {~(c=c)} closes by reflexivity resolution alone
    # (u=v=c unify trivially).
    assert is_valid_resolution(EQ(c, c), max_steps=2000) is True


def test_reflexivity_combined_with_an_ordinary_predicate_fact():
    # {forall x P(x,x)} |= exists x exists y (P(x,y) and x=y): a genuinely
    # equality-flavoured goal (not just P(c,c)) that needs BOTH the ordinary
    # P(x,x) fact (via plain unification, no equality machinery) AND
    # reflexivity resolution to close. Clausified: premise {P(z,z)} (z the
    # premise's own variable); negated goal, after Skolemising the two
    # existentials to fresh constants sk0, sk1, is {~P(sk0,sk1), ~(sk0=sk1)}.
    # Resolving P(z,z) against ~P(sk0,sk1) (mgu z->sk0, sk1->sk0, i.e.
    # sk0=sk1 identified) leaves {~(sk0=sk0)}, which reflexivity resolution
    # then empties.
    premise = Quantifier("forall", x, P(x, x))
    goal = Quantifier("exists", x,
                       Quantifier("exists", y, And(P(x, y), EQ(x, y))))
    assert prove([premise], goal, max_steps=2000) is True


# --- (f) A small, genuinely nontrivial equational lemma from group axioms ---
#
# Axioms (only LEFT identity and LEFT inverse — no associativity, no
# right-identity/right-inverse assumed): e*x = x, i(x)*x = e.
# Goal: e*(i(a)*a) = e.
#
# Hand derivation: {i(x)*x=e} has weight(i(x)*x)=4 > weight(e)=1, so it
# orients (i(x)*x -> e); instantiating x:=a rewrites the 'i(a)*a' subterm of
# the negated goal's LHS, giving ~(e*e=e). {e*x=x} has weight(e*x)=3 >
# weight(x)=1, orienting (e*x -> x); instantiating x:=e rewrites 'e*e' to
# 'e', giving ~(e=e), which reflexivity resolution closes. Two
# paramodulations + one reflexivity — fast (well under a second, confirmed
# by direct timing), so no budget concession is needed here.

def test_group_axiom_lemma_provable():
    e = Constant("e")
    mul = lambda s, t: Function("*", [s, t])
    inv = lambda t: Function("i", [t])
    left_identity = Quantifier("forall", x, EQ(mul(e, x), x))
    left_inverse = Quantifier("forall", x, EQ(mul(inv(x), x), e))
    goal = EQ(mul(e, mul(inv(a), a)), e)
    assert prove([left_identity, left_inverse], goal, max_steps=5000) is True


# --- (g) NEGATIVE: soundness guard, a non-theorem stays unproved ---

def test_unrelated_equality_is_not_entailed():
    # {a=b} does NOT entail a=c: b and c are unrelated constants, nothing
    # links them. The clause set {a=b, ~(a=c)} saturates (no productive
    # paramodulation target exists — 'b' never occurs in ~(a=c), and a, c do
    # not unify for reflexivity) without ever deriving the empty clause.
    assert prove([EQ(a, b)], EQ(a, c), max_steps=2000) is False


def test_negated_congruence_goal_still_sound():
    # Soundness guard for the newly added machinery specifically: {a=b} must
    # NOT entail f(a)=f(c) (only f(a)=f(b) is a genuine consequence).
    assert prove([EQ(a, b)], EQ(f(a), f(c)), max_steps=2000) is False


# ---------------------------------------------------------------------------
# 5. Round trips: hand-built ResolutionDerivation certificates for several of
#    the proofs above, each independently re-verified by
#    verify_resolution_proof — plus a standalone certificate for
#    demodulate (which none of the end-to-end proofs above happen to need as
#    an essential step) and the rejection of the removed self_paramodulate.
# ---------------------------------------------------------------------------

def test_roundtrip_congruence():
    # Matches test_congruence_provable's hand derivation exactly.
    C1 = frozenset({EQ(a, b)})
    C2 = frozenset({Not(EQ(f(a), f(b)))})
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset({Not(EQ(f(a), f(a)))}), "paramodulate", (1, 2),
                        eq_literal=EQ(a, b), target_literal=Not(EQ(f(a), f(b))),
                        direction="rl", position=(1, 0)),
        ResolutionStep(4, frozenset(), "reflexivity", (3,),
                        eq_literal=Not(EQ(f(a), f(a)))),
    )
    d = ResolutionDerivation((C1, C2), steps)
    r = verify_resolution_proof(d)
    assert r.ok, r.error
    assert r.refuted is True
    expected_render = (
        "1. a = b [input]\n"
        "2. ¬f(a) = f(b) [input]\n"
        "3. ¬f(a) = f(a) [paramodulate 1,2]\n"
        "4. □ [reflexivity 3]"
    )
    assert render_resolution_proof(d) == expected_render


def test_roundtrip_transitivity_and_symmetry():
    # Matches test_transitivity_and_symmetry_chain_provable's derivation.
    C1 = frozenset({EQ(a, b)})
    C2 = frozenset({EQ(b, c)})
    C3 = frozenset({Not(EQ(c, a))})
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, C3, "input"),
        ResolutionStep(4, frozenset({Not(EQ(b, a))}), "paramodulate", (2, 3),
                        eq_literal=EQ(b, c), target_literal=Not(EQ(c, a)),
                        direction="rl", position=(0,)),
        ResolutionStep(5, frozenset({Not(EQ(a, a))}), "paramodulate", (1, 4),
                        eq_literal=EQ(a, b), target_literal=Not(EQ(b, a)),
                        direction="rl", position=(0,)),
        ResolutionStep(6, frozenset(), "reflexivity", (5,),
                        eq_literal=Not(EQ(a, a))),
    )
    d = ResolutionDerivation((C1, C2, C3), steps)
    r = verify_resolution_proof(d)
    assert r.ok, r.error
    assert r.refuted is True


def test_roundtrip_paramodulation_into_predicate():
    # Matches test_paramodulation_into_predicate_provable's derivation:
    # paramodulate, then an ordinary "resolve" step.
    C1 = frozenset({EQ(a, b)})
    C2 = frozenset({P(a)})
    C3 = frozenset({Not(P(b))})
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, C3, "input"),
        ResolutionStep(4, frozenset({Not(P(a))}), "paramodulate", (1, 3),
                        eq_literal=EQ(a, b), target_literal=Not(P(b)),
                        direction="rl", position=(0,)),
        ResolutionStep(5, frozenset(), "resolve", (2, 4)),
    )
    d = ResolutionDerivation((C1, C2, C3), steps)
    r = verify_resolution_proof(d)
    assert r.ok, r.error
    assert r.refuted is True


def test_checker_rejects_the_removed_self_paramodulate_rule():
    """A derivation claiming the UNSOUND shared-instance rule must be
    rejected as an unknown rule — never re-derived. This is exactly the
    step the removed shortcut used to certify ({a=b, ¬P(b)} ⇒ {¬P(a)}),
    which is false in the model a≠b, P(b)=false, P(a)=true. The error
    message enumerates the actual rule vocabulary (generated from
    _RULE_ARITY so it can never drift again — second review finding)."""
    C1 = frozenset({EQ(a, b), Not(P(b))})
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, frozenset({Not(P(a))}), "self_paramodulate", (1,),
                        eq_literal=EQ(a, b), target_literal=Not(P(b)),
                        direction="rl", position=(0,)),
    )
    r = verify_resolution_proof(ResolutionDerivation((C1,), steps))
    assert r.ok is False
    assert r.error_index == 2
    assert "unknown rule 'self_paramodulate'" in r.error
    for rule in ("'input'", "'resolve'", "'factor'", "'paramodulate'",
                 "'reflexivity'", "'demodulate'"):
        assert rule in r.error


def test_roundtrip_demodulate():
    # Standalone certificate for "demodulate", matching
    # test_demodulate_once_and_fixpoint_pinned's rule {f(x)=a} (oriented
    # f(x) -> a) simplifying P(f(b)) to P(a).
    target = frozenset({P(f(b))})
    unit_eq = frozenset({EQ(f(x), a)})
    steps = (
        ResolutionStep(1, target, "input"),
        ResolutionStep(2, unit_eq, "input"),
        ResolutionStep(3, frozenset({P(a)}), "demodulate", (1, 2),
                        eq_literal=EQ(f(x), a), target_literal=P(f(b)),
                        direction="lr", position=(0,)),
    )
    d = ResolutionDerivation((target, unit_eq), steps)
    r = verify_resolution_proof(d)
    assert r.ok, r.error


# ---------------------------------------------------------------------------
# 6. TAMPER cases: a manipulated step must be rejected with a precise error.
#    Covers all three new rule kinds (paramodulate x3, reflexivity x1,
#    demodulate x3) -- 7 cases total, over the required minimum of 6.
# ---------------------------------------------------------------------------

def _congruence_inputs():
    C1 = frozenset({EQ(a, b)})
    C2 = frozenset({Not(EQ(f(a), f(b)))})
    return C1, C2


def test_tamper_paramodulate_wrong_position():
    # The real rewrite happens at position (1,0) [the 'b' inside f(b)];
    # (0,0) addresses 'a' inside f(a), which does not unify with 'b'.
    C1, C2 = _congruence_inputs()
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset({Not(EQ(f(a), f(a)))}), "paramodulate", (1, 2),
                        eq_literal=EQ(a, b), target_literal=Not(EQ(f(a), f(b))),
                        direction="rl", position=(0, 0)),
    )
    r = verify_resolution_proof(ResolutionDerivation((C1, C2), steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "does not unify with the subterm at position" in r.error


def test_tamper_paramodulate_wrong_direction():
    # direction "lr" makes frm=a, which does not occur anywhere in the
    # target atom f(a)=f(b) at a MATCHING position for unifying with the
    # equation's 'a' side against 'b' — position (1,0) holds 'b', not 'a'.
    C1, C2 = _congruence_inputs()
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset({Not(EQ(f(a), f(a)))}), "paramodulate", (1, 2),
                        eq_literal=EQ(a, b), target_literal=Not(EQ(f(a), f(b))),
                        direction="lr", position=(1, 0)),
    )
    r = verify_resolution_proof(ResolutionDerivation((C1, C2), steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "does not unify with the subterm at position" in r.error


def test_tamper_paramodulate_falsified_remainder():
    # Correct position/direction/unifier, but the CLAIMED clause is wrong
    # (c instead of a) -- the recomputation succeeds but disagrees.
    C1, C2 = _congruence_inputs()
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset({Not(EQ(f(a), c))}), "paramodulate", (1, 2),
                        eq_literal=EQ(a, b), target_literal=Not(EQ(f(a), f(b))),
                        direction="rl", position=(1, 0)),
    )
    r = verify_resolution_proof(ResolutionDerivation((C1, C2), steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "not a variant of the stated clause" in r.error


def test_tamper_paramodulate_equality_literal_from_wrong_parent():
    # eq_literal claims "a=c", but the cited equation parent (clause 1) is
    # really {a=b} -- "a=c" is not present in it.
    C1, C2 = _congruence_inputs()
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset({Not(EQ(f(a), f(a)))}), "paramodulate", (1, 2),
                        eq_literal=EQ(a, c), target_literal=Not(EQ(f(a), f(b))),
                        direction="rl", position=(1, 0)),
    )
    r = verify_resolution_proof(ResolutionDerivation((C1, C2), steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "not present in the cited equation parent" in r.error


def test_tamper_reflexivity_on_non_unifiable_terms():
    # a and c are distinct constants: no unifier, so reflexivity cannot
    # apply, however the derivation claims it does.
    C1 = frozenset({Not(EQ(a, c))})
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, frozenset(), "reflexivity", (1,),
                        eq_literal=Not(EQ(a, c))),
    )
    r = verify_resolution_proof(ResolutionDerivation((C1,), steps))
    assert r.ok is False
    assert r.error_index == 2
    assert "do not unify" in r.error


def test_tamper_demodulate_direction_against_the_order():
    # {a=b} is oriented (b -> a) by the term order (b > a); direction "lr"
    # claims the opposite (a -> b). The match itself succeeds (target
    # contains 'a'), but the orientation check must still reject it.
    target = frozenset({P(a)})
    unit_eq = frozenset({EQ(a, b)})
    steps = (
        ResolutionStep(1, target, "input"),
        ResolutionStep(2, unit_eq, "input"),
        ResolutionStep(3, frozenset({P(b)}), "demodulate", (1, 2),
                        eq_literal=EQ(a, b), target_literal=P(a),
                        direction="lr", position=(0,)),
    )
    r = verify_resolution_proof(ResolutionDerivation((target, unit_eq), steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "orientation does not strictly decrease" in r.error


def test_tamper_demodulate_non_unit_equation_parent():
    # The cited equation parent {a=b, Q(c)} is NOT a unit clause -- it only
    # asserts a=b OR Q(c), so using it as an unconditional rewrite rule
    # would be unsound; the checker must refuse regardless of whether the
    # rewrite itself would otherwise check out.
    target = frozenset({P(b)})
    non_unit = frozenset({EQ(a, b), Q(c)})
    steps = (
        ResolutionStep(1, target, "input"),
        ResolutionStep(2, non_unit, "input"),
        ResolutionStep(3, frozenset({P(a)}), "demodulate", (1, 2),
                        eq_literal=EQ(a, b), target_literal=P(b),
                        direction="rl", position=(0,)),
    )
    r = verify_resolution_proof(ResolutionDerivation((target, non_unit), steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "must be a UNIT clause" in r.error


# ---------------------------------------------------------------------------
# 7. Differential check: resolution.py's and resolution_check.py's
#    independently reimplemented term orders must agree on any given pair —
#    the same independence discipline test_resolution_check.py's
#    differential unification battery already applies to _unify/unify.
# ---------------------------------------------------------------------------

_ORDER_BATTERY = [
    (a, b), (b, a), (a, a),
    (f(a), a), (f(x), x),
    (g(x), f(x)), (f(x), g(x)),
    (Function("h", [a, b]), f(a)),
]


def test_differential_term_order_battery():
    for s, t in _ORDER_BATTERY:
        assert _term_gt(s, t) == _check_term_gt(s, t), (
            f"resolution._term_gt and resolution_check._term_gt disagreed "
            f"on {s.to_unicode_str()} vs {t.to_unicode_str()}"
        )
