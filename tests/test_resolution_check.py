"""Tests for the independent resolution-proof checker (unicode_fol_kit.atp.resolution_check).

Every expected value below is hand-derived (see the comment above each
assertion for the derivation) rather than taken from running the checker
first. Two families of tests target the module's two deliberate independence
requirements (see its module docstring):

- A differential battery comparing the checker's own :func:`_unify` against
  :func:`unicode_fol_kit.fol.unification.unify` on unifiable/non-unifiable atom
  pairs (independence requirement 1).
- Hand-checked trap cases plus a reflexivity/symmetry/transitivity sweep for
  the exact backtracking variant (alpha-equivalence) search, :func:`_is_variant`
  (independence requirement 2).

Plus a differential end-to-end check against the searcher
(:func:`unicode_fol_kit.atp.resolution.prove`): for formula sets it proves,
hand-built resolution derivations for the SAME refutation must verify.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, Implies, Or, Variable, Constant, Function,
)
from unicode_fol_kit.fol.unification import unify as kit_unify, apply_subst as kit_apply_subst
from unicode_fol_kit.atp.resolution import prove
from unicode_fol_kit.atp.resolution_check import (
    ResolutionStep, ResolutionDerivation, ResolutionCheckResult,
    verify_resolution_proof, check_resolution_proof, render_resolution_proof,
    _unify, _apply, _is_variant,
)


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


def R(*args):
    return Atom("R", list(args))


x, y, u, v = Variable("x"), Variable("y"), Variable("u"), Variable("v")
a, b = Constant("a"), Constant("b")


def f(t):
    return Function("f", [t])


def g(t):
    return Function("g", [t])


# ---------------------------------------------------------------------------
# (a) End-to-end FOL refutation, hand-derived
#
#   {P(a)}, {¬P(x) ∨ Q(x)}, {¬Q(a)}  is unsatisfiable:
#     4. resolve(1,2) on P(a)/¬P(x), mgu {x↦a}: (∅ ∖ P(a)) ∪ ({Q(x)} ∖ {}) [x↦a]
#        = {Q(a)}
#     5. resolve(3,4) on ¬Q(a)/Q(a), mgu {} (identical ground atoms): {} ∪ {} = ∅
# ---------------------------------------------------------------------------

def _part_a_derivation():
    inputs = (frozenset({P(a)}), frozenset({Not(P(x)), Q(x)}), frozenset({Not(Q(a))}))
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({Not(P(x)), Q(x)}), "input"),
        ResolutionStep(3, frozenset({Not(Q(a))}), "input"),
        ResolutionStep(4, frozenset({Q(a)}), "resolve", (1, 2)),
        ResolutionStep(5, frozenset(), "resolve", (3, 4)),
    )
    return ResolutionDerivation(inputs, steps)


def test_end_to_end_fol_refutation():
    d = _part_a_derivation()
    r = verify_resolution_proof(d)
    assert r.ok, r.error
    assert r.error_index is None and r.error is None
    assert r.refuted is True
    assert check_resolution_proof(d) is True
    assert bool(r) is True


# ---------------------------------------------------------------------------
# (e) render_resolution_proof, pinned for the part-(a) refutation.
#
# Hand-derivation of the expected string: each literal renders via
# to_unicode_str() (Atom "P(a)"; Not(Atom) "¬P(x)"; nullary-arg atoms render
# with no comma, e.g. "Q(x)"); a 2-literal clause is sorted by that rendered
# string, and 'Q' (U+0051) sorts before '¬' (U+00AC) codepoint-wise, so
# {¬P(x), Q(x)} renders "Q(x) ∨ ¬P(x)". The empty clause renders "□".
# ---------------------------------------------------------------------------

def test_render_resolution_proof_pinned():
    d = _part_a_derivation()
    expected = (
        "1. P(a) [input]\n"
        "2. Q(x) ∨ ¬P(x) [input]\n"
        "3. ¬Q(a) [input]\n"
        "4. Q(a) [resolve 1,2]\n"
        "5. □ [resolve 3,4]"
    )
    assert render_resolution_proof(d) == expected


# ---------------------------------------------------------------------------
# (b) Factoring: {P(x), P(y)} -> factor -> {P(x)} accepted.
#
# Hand-derivation: unify(P(x), P(y)) has mgu {x↦y} (or {y↦x}, depending on
# which side the algorithm treats as t1 first); applying it to the clause
# collapses both literals into a single-variable atom, which is a variant of
# the declared {P(x)} (any single-variable unary atom is trivially a variant
# of any other — both are "one free slot", renamed by the bijection).
# ---------------------------------------------------------------------------

def test_factoring_simple_accepted():
    inputs = (frozenset({P(x), P(y)}),)
    steps = (
        ResolutionStep(1, frozenset({P(x), P(y)}), "input"),
        ResolutionStep(2, frozenset({P(x)}), "factor", (1,)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok, r.error


# ---------------------------------------------------------------------------
# (b) Classic Robinson example: {P(x), P(y)} and {¬P(u), ¬P(v)}.
#
# Direct resolution (no factoring) can only ever cancel ONE literal from each
# side, e.g. resolve on P(x)/¬P(u) with mgu {x↦u} leaves {P(y), ¬P(v)} — a
# genuine 2-literal clause, never the empty clause, no matter which of the
# four complementary pairs is picked (P(x)/¬P(u), P(x)/¬P(v), P(y)/¬P(u),
# P(y)/¬P(v) are the only four; each leaves exactly the other two literals).
# Refutation REQUIRES factoring each clause down to a unit clause first:
#   factor(1) on P(x)/P(y), mgu {x↦y}: {P(y)}  (declared as the variant {P(x)})
#   factor(2) on ¬P(u)/¬P(v), mgu {u↦v}: {¬P(v)}  (declared as {¬P(u)})
#   resolve(factored 1, factored 2) on P(x)/¬P(u), mgu {x↦u}: ∅ ∪ ∅ = ∅
# ---------------------------------------------------------------------------

def _robinson_inputs():
    return (frozenset({P(x), P(y)}), frozenset({Not(P(u)), Not(P(v))}))


def test_robinson_direct_resolution_is_not_a_refutation():
    """A correctly-checked direct resolvent is a genuine 2-literal clause, not ∅."""
    inputs = _robinson_inputs()
    steps = (
        ResolutionStep(1, frozenset({P(x), P(y)}), "input"),
        ResolutionStep(2, frozenset({Not(P(u)), Not(P(v))}), "input"),
        ResolutionStep(3, frozenset({P(y), Not(P(v))}), "resolve", (1, 2)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok, r.error
    assert r.refuted is False  # accepted, but not a refutation


def test_robinson_direct_empty_clause_claim_is_rejected():
    """Claiming the empty clause directly from (1,2) WITHOUT factoring must fail."""
    inputs = _robinson_inputs()
    steps = (
        ResolutionStep(1, frozenset({P(x), P(y)}), "input"),
        ResolutionStep(2, frozenset({Not(P(u)), Not(P(v))}), "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "resolve" in r.error


def test_robinson_factored_refutation_accepted():
    inputs = _robinson_inputs()
    steps = (
        ResolutionStep(1, frozenset({P(x), P(y)}), "input"),
        ResolutionStep(2, frozenset({Not(P(u)), Not(P(v))}), "input"),
        ResolutionStep(3, frozenset({P(x)}), "factor", (1,)),
        ResolutionStep(4, frozenset({Not(P(u))}), "factor", (2,)),
        ResolutionStep(5, frozenset(), "resolve", (3, 4)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok, r.error
    assert r.refuted is True


# ---------------------------------------------------------------------------
# (c) Rejection cases, each pinning the actual error message.
# ---------------------------------------------------------------------------

def test_reject_wrong_resolvent_clause():
    # {P(a)} resolved with {¬P(x), Q(x)} on P(a)/¬P(x) can only give {Q(a)}
    # ([x↦a]); {Q(b)} is a different (unrelated) ground atom, not a variant.
    inputs = (frozenset({P(a)}), frozenset({Not(P(x)), Q(x)}))
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({Not(P(x)), Q(x)}), "input"),
        ResolutionStep(3, frozenset({Q(b)}), "resolve", (1, 2)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "mgu produces the stated resolvent clause" in r.error


def test_reject_same_polarity_resolve():
    # {P(a)} and {P(x)} are BOTH positive: no complementary-polarity pair
    # exists at all, which is a distinct failure from "wrong resolvent".
    inputs = (frozenset({P(a)}), frozenset({P(x)}))
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({P(x)}), "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "no complementary-polarity literal pair" in r.error


def test_reject_ununifiable_occurs_check():
    # P(x, f(x)) vs ¬P(y, y): unifying arg0 gives x↦y, then arg1 needs
    # f(x)~y i.e. (after x↦y) f(y)~y, which fails the occurs-check (y occurs
    # in f(y)) -- P(x) vs P(f(x)) is the textbook occurs-check failure, here
    # reached transitively through a shared clause variable.
    Pxy = lambda s, t: Atom("P", [s, t])
    inputs = (frozenset({Pxy(x, f(x))}), frozenset({Not(Pxy(y, y))}))
    steps = (
        ResolutionStep(1, frozenset({Pxy(x, f(x))}), "input"),
        ResolutionStep(2, frozenset({Not(Pxy(y, y))}), "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "resolve" in r.error


def test_reject_parent_index_not_strictly_earlier():
    # Step 2 cites itself as a parent (index 2 >= step index 2).
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset(), "resolve", (1, 2)),
    )
    r = verify_resolution_proof(ResolutionDerivation((frozenset({P(a)}),), steps))
    assert r.ok is False
    assert r.error_index == 2
    assert "strictly earlier" in r.error


def test_reject_rule_arity_mismatch():
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({P(a)}), "resolve", (1,)),  # resolve needs 2 parents
    )
    r = verify_resolution_proof(ResolutionDerivation((frozenset({P(a)}),), steps))
    assert r.ok is False
    assert r.error_index == 2
    assert "takes 2 parent(s), got 1" in r.error


def test_reject_unknown_rule():
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({P(a)}), "bogus", (1,)),
    )
    r = verify_resolution_proof(ResolutionDerivation((frozenset({P(a)}),), steps))
    assert r.ok is False
    assert r.error_index == 2
    assert "unknown rule" in r.error


def test_reject_input_clause_not_among_inputs():
    steps = (ResolutionStep(1, frozenset({Q(a)}), "input"),)
    r = verify_resolution_proof(ResolutionDerivation((frozenset({P(a)}),), steps))
    assert r.ok is False
    assert r.error_index == 1
    assert "not a variant" in r.error


def test_reject_step_index_not_matching_position():
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(3, frozenset({P(a)}), "input"),  # should be 2
    )
    r = verify_resolution_proof(ResolutionDerivation((frozenset({P(a)}),), steps))
    assert r.ok is False
    assert r.error_index == 3
    assert "expected 2" in r.error


# ---------------------------------------------------------------------------
# (d) A resolve step needing standardizing-apart: BOTH parents use variable x.
#
# {P(x)} and {¬P(f(x))} use "x" as each clause's own (independent) bound
# variable. WITHOUT renaming apart first, unifying P(x) against P(f(x))
# directly would hit the occurs-check (x occurs in f(x)) and wrongly reject a
# sound step. WITH standardizing apart (x -> _L0 in one, x -> _R0 in the
# other), the unification is P(_L0)/P(f(_R0)), mgu {_L0 ↦ f(_R0)} (no
# occurs-check issue, _L0 and _R0 are different variables), giving the empty
# clause: (∅) ∪ (∅) = ∅.
# ---------------------------------------------------------------------------

def test_resolve_requires_standardizing_apart():
    inputs = (frozenset({P(x)}), frozenset({Not(P(f(x)))}))
    steps = (
        ResolutionStep(1, frozenset({P(x)}), "input"),
        ResolutionStep(2, frozenset({Not(P(f(x)))}), "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok, r.error
    assert r.refuted is True


# ---------------------------------------------------------------------------
# Empty derivation and thin-wrapper / __bool__ sanity.
# ---------------------------------------------------------------------------

def test_empty_step_list_ok_and_not_refuted():
    r = verify_resolution_proof(ResolutionDerivation((frozenset({P(a)}),), ()))
    assert r.ok is True
    assert r.refuted is False
    assert r.error_index is None and r.error is None


def test_check_resolution_proof_is_thin_wrapper():
    d = _part_a_derivation()
    assert check_resolution_proof(d) == verify_resolution_proof(d).ok
    bad = ResolutionDerivation((frozenset({P(a)}),), (ResolutionStep(1, frozenset({Q(a)}), "input"),))
    assert check_resolution_proof(bad) is False


def test_resolution_check_result_bool():
    ok_result = verify_resolution_proof(_part_a_derivation())
    bad = ResolutionDerivation((frozenset({P(a)}),), (ResolutionStep(1, frozenset({Q(a)}), "input"),))
    bad_result = verify_resolution_proof(bad)
    assert bool(ok_result) is True
    assert bool(bad_result) is False


def test_step_and_derivation_coerce_iterables():
    # clause/parents/inputs/steps accept plain list/set inputs and are
    # normalised to frozenset/tuple, matching the frozen-dataclass house rule.
    step = ResolutionStep(1, [P(a)], "input", [])
    assert isinstance(step.clause, frozenset)
    assert isinstance(step.parents, tuple)
    d = ResolutionDerivation([{P(a)}], [step])
    assert isinstance(d.inputs, tuple) and isinstance(d.inputs[0], frozenset)
    assert isinstance(d.steps, tuple)
    assert verify_resolution_proof(d).ok


# ---------------------------------------------------------------------------
# Independence requirement 1: differential unification battery.
#
# 14 hand-picked atom pairs covering: a simple ground instantiation; distinct
# constants (fail); an occurs-check failure in both argument orders; a
# variable/variable cycle P(x,y)~P(y,x) (succeeds, both variables end up
# equated); a repeated-variable clash P(x,x)~P(a,b) (fail, x can't be both);
# a repeated-variable success P(x,x)~P(a,a); nested-function success; a
# binding that fails only once propagated across two argument positions
# (P(f(x),x)~P(f(a),b)); two free variables unifying with each other;
# repeated-variable-through-nested-function success (Skolem-style); a
# function-symbol clash despite a shared variable; a predicate-name mismatch;
# and a deeper occurs-check nested two levels down.
#
# For EACH pair: the checker's _unify and the kit's unify() must AGREE on
# unifiability, and wherever a substitution is produced, applying that same
# substitution to both atoms (via the matching apply function) must yield
# syntactically equal results -- the defining property of a unifier.
# ---------------------------------------------------------------------------

_UNIFY_BATTERY = [
    (P(x), P(a), True),
    (P(a), P(b), False),
    (P(x), P(f(x)), False),
    (P(f(x)), P(x), False),
    (P(x, y), P(y, x), True),
    (P(x, x), P(a, b), False),
    (P(x, x), P(a, a), True),
    (P(f(x), g(y)), P(f(a), g(b)), True),
    (P(f(x), x), P(f(a), b), False),
    (P(x), P(y), True),
    (Q(x, f(x)), Q(g(y), f(g(y))), True),
    (P(f(x)), P(g(x)), False),
    (P(x), Q(x), False),
    (P(x), P(f(g(x))), False),
]


@pytest.mark.parametrize("atom1, atom2, expected_unifiable", _UNIFY_BATTERY)
def test_differential_unify_battery(atom1, atom2, expected_unifiable):
    checker_subst = _unify(atom1, atom2)
    kit_subst = kit_unify(atom1, atom2)
    checker_ok = checker_subst is not None
    kit_ok = kit_subst is not None

    assert checker_ok == expected_unifiable, (
        f"_unify disagreed with the hand-derived expectation for "
        f"{atom1.to_unicode_str()} ~ {atom2.to_unicode_str()}"
    )
    assert checker_ok == kit_ok, (
        f"_unify and fol.unification.unify disagreed on unifiability for "
        f"{atom1.to_unicode_str()} ~ {atom2.to_unicode_str()}"
    )

    if checker_ok:
        assert _apply(atom1, checker_subst) == _apply(atom2, checker_subst)
    if kit_ok:
        assert kit_apply_subst(atom1, kit_subst) == kit_apply_subst(atom2, kit_subst)


def test_unify_battery_has_at_least_12_pairs():
    assert len(_UNIFY_BATTERY) >= 12
    assert any(expected for *_, expected in _UNIFY_BATTERY)
    assert any(not expected for *_, expected in _UNIFY_BATTERY)


# ---------------------------------------------------------------------------
# Independence requirement 2: exact variant (alpha-equivalence) checking.
# ---------------------------------------------------------------------------

def test_variant_trap_2cycle_is_a_variant():
    # {P(x,y), P(y,x)} IS a variant of {P(u,v), P(v,u)}: match P(x,y)~P(u,v)
    # (bijection x<->u, y<->v so far), then the SECOND literal P(y,x) must
    # match the remaining P(v,u) under that SAME bijection: (y,x) -> (v,u) --
    # y already maps to v and x already maps to u, so it checks out.
    a_clause = frozenset({P(x, y), P(y, x)})
    b_clause = frozenset({P(u, v), P(v, u)})
    assert _is_variant(a_clause, b_clause) is True


def test_variant_trap_repeated_var_not_variant_of_distinct_vars():
    # {P(x,x)} is NOT a variant of {P(x,y)}: the single literal P(x,x) would
    # need its (only) variable to map onto BOTH x and y of P(x,y) at once,
    # which is impossible for a variable-name bijection (a function, not a
    # relation) -- {P(x,x)} says "P holds of some individual paired with
    # itself", {P(x,y)} says "P holds of a possibly-DIFFERENT pair".
    assert _is_variant(frozenset({P(x, x)}), frozenset({P(x, y)})) is False


def test_variant_trap_constant_is_not_a_variable():
    # {P(x)} vs {P(a)}: a is a Constant, not a Variable -- no variable-name
    # bijection can ever match a bound variable position to a fixed ground
    # constant, since the bijection is only defined over variable NAMES.
    assert _is_variant(frozenset({P(x)}), frozenset({P(a)})) is False
    assert _is_variant(frozenset({P(a)}), frozenset({P(x)})) is False  # symmetric


_VARIANT_TEST_SET = [
    frozenset({P(a)}),
    frozenset({P(x)}),
    frozenset({P(x), Q(x)}),
    frozenset({P(x), P(y)}),
    frozenset({P(x, y), P(y, x)}),
    frozenset({P(u, v), P(v, u)}),
    frozenset({P(x, x)}),
    frozenset({P(x, y)}),
    frozenset(),
    frozenset({Not(P(x)), Q(x)}),
    frozenset({P(f(x))}),
    frozenset({P(f(a))}),
]


def test_variant_is_reflexive_on_test_set():
    for clause in _VARIANT_TEST_SET:
        assert _is_variant(clause, clause) is True


def test_variant_is_symmetric_on_test_set():
    for i, ca in enumerate(_VARIANT_TEST_SET):
        for cb in _VARIANT_TEST_SET[i:]:
            assert _is_variant(ca, cb) == _is_variant(cb, ca), (ca, cb)


def test_variant_is_transitive_on_test_set():
    for ca in _VARIANT_TEST_SET:
        for cb in _VARIANT_TEST_SET:
            if not _is_variant(ca, cb):
                continue
            for cc in _VARIANT_TEST_SET:
                if _is_variant(cb, cc):
                    assert _is_variant(ca, cc), (ca, cb, cc)


def test_variant_alpha_equivalent_renaming_pairs():
    # A single-variable renaming of a genuinely first-order clause must
    # still be recognised, including through a function-symbol argument.
    assert _is_variant(frozenset({P(f(x))}), frozenset({P(f(y))})) is True
    assert _is_variant(frozenset({P(f(x))}), frozenset({P(f(a))})) is False


# ---------------------------------------------------------------------------
# Differential end-to-end test: for formula sets atp.resolution.prove(...)
# proves, a hand-built derivation for the SAME refutation must verify --
# checker and searcher must agree on what resolution IS.
# ---------------------------------------------------------------------------

def test_differential_prove_trivial_identity():
    # P(a) |= P(a): clausify the premise {P(a)} and the negated conclusion
    # {¬P(a)}; they resolve directly to the empty clause.
    assert prove([P(a)], P(a)) is True
    inputs = (frozenset({P(a)}), frozenset({Not(P(a))}))
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({Not(P(a))}), "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok and r.refuted, r.error


def test_differential_prove_modus_ponens():
    # (Pprop -> Qprop), Pprop |= Qprop, using nullary propositional atoms.
    # Clausify: (Pprop->Qprop) -> {¬Pprop, Qprop}; Pprop -> {Pprop};
    # ¬Qprop (negated conclusion) -> {¬Qprop}.
    Pprop, Qprop = Atom("P", []), Atom("Q", [])
    assert prove([Implies(Pprop, Qprop), Pprop], Qprop) is True
    inputs = (frozenset({Not(Pprop), Qprop}), frozenset({Pprop}), frozenset({Not(Qprop)}))
    steps = (
        ResolutionStep(1, frozenset({Not(Pprop), Qprop}), "input"),
        ResolutionStep(2, frozenset({Pprop}), "input"),
        ResolutionStep(3, frozenset({Not(Qprop)}), "input"),
        ResolutionStep(4, frozenset({Qprop}), "resolve", (2, 1)),
        ResolutionStep(5, frozenset(), "resolve", (4, 3)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok and r.refuted, r.error


def test_differential_prove_constructive_dilemma():
    # (P(a) v Q(a)), (P(a)->R(a)), (Q(a)->R(a)) |= R(a).
    # Clausify: {P(a),Q(a)}, {¬P(a),R(a)}, {¬Q(a),R(a)}, negated goal {¬R(a)}.
    Pa, Qa, Ra = P(a), Q(a), R(a)
    premises = [Or(Pa, Qa), Implies(Pa, Ra), Implies(Qa, Ra)]
    assert prove(premises, Ra) is True
    inputs = (
        frozenset({Pa, Qa}),
        frozenset({Not(Pa), Ra}),
        frozenset({Not(Qa), Ra}),
        frozenset({Not(Ra)}),
    )
    steps = (
        ResolutionStep(1, frozenset({Pa, Qa}), "input"),
        ResolutionStep(2, frozenset({Not(Pa), Ra}), "input"),
        ResolutionStep(3, frozenset({Not(Qa), Ra}), "input"),
        ResolutionStep(4, frozenset({Not(Ra)}), "input"),
        # resolve(1,2) on P(a)/¬P(a): {Qa} ∪ {Ra} = {Qa, Ra}
        ResolutionStep(5, frozenset({Qa, Ra}), "resolve", (1, 2)),
        # resolve(5,3) on Q(a)/¬Q(a): {Ra} ∪ {Ra} = {Ra} (duplicate collapses)
        ResolutionStep(6, frozenset({Ra}), "resolve", (5, 3)),
        # resolve(6,4) on R(a)/¬R(a): {} ∪ {} = {}
        ResolutionStep(7, frozenset(), "resolve", (6, 4)),
    )
    r = verify_resolution_proof(ResolutionDerivation(inputs, steps))
    assert r.ok and r.refuted, r.error
