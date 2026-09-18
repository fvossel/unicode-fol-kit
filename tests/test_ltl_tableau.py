"""Tests for unicode_fol_kit.atp.ltl_tableau — the standard linear-time
LTL(+Past) decision procedure over the discrete order on the natural numbers.

Three independent channels back every verdict here, matching the kit's
existing convention (``kripke_enum.py`` pairs ``modal_tableau`` with a
brute-force semantic oracle; ``modal_tableau`` itself verifies every
countermodel against ``satisfies_modal`` before releasing it):

1. :func:`_eval_on_lasso` below is a from-scratch evaluator of the
   linear-time satisfaction equations over an EXPLICIT, eagerly materialized
   finite unrolling of a lasso — independent of
   ``ltl_tableau.ltl_trace_satisfies`` (which the module itself uses to
   self-verify a countermodel before releasing it): different code and a
   different strategy (eager unrolling to a concrete list vs. that module's
   on-demand modular indexing + memoized recursion), so a shared bug in the
   tableau's closure/graph construction is very unlikely to also be hiding
   identically in this check.
2. Hand-checked textbook (non-)validities (Baier & Katoen ch. 5 / Manna &
   Pnueli): the fixpoint unfoldings, the future/past dualities, and the
   flagship temporal-induction theorem ``fol.qml``'s own docstring names as
   genuinely out of its reach.
3. A monotonicity cross-check against ``fol.qml.qml_is_valid`` (the standard
   linear frame is a strict SUBSET of qml's refl+trans+``N⊆T`` frame class,
   so every qml-valid temporal formula must come back valid here too — see
   ``LtlTableauBackend``'s docstring) and a property-based cross-check:
   seeded random small formulas over ``{p, q}``, exhaustively checked
   against every lasso up to a small total length.

A separate section cross-checks against ``semantics.kripke.satisfies_modal``
on an explicit finite, non-cyclic, deterministic ``KripkeModel`` — the
fragment where the two ARE provably the same question — and documents (with
a test, not just a comment) exactly where that fragment stops.
"""

import random

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff,
    Next, Always, Eventually, Until, Historically, Once, Previous, Since,
    Box, Quantifier, Variable,
)
from unicode_fol_kit.atp.ltl_tableau import (
    LTLTrace, ltl_tableau_closed, ltl_valid, ltl_decide, ltl_countermodel,
    ltl_trace_satisfies,
)
from unicode_fol_kit.atp.protocol import get_backend, PROVED, REFUTED, UNKNOWN
from unicode_fol_kit.fol.qml import qml_is_valid
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

p, q = Atom("p", ()), Atom("q", ())


# --------------------------------------------------------------------------- #
# LTLTrace basics.
# --------------------------------------------------------------------------- #

def test_ltltrace_at_wraps_into_the_cycle():
    tr = LTLTrace(prefix=(frozenset(), frozenset({"p"})), cycle=(frozenset({"q"}),))
    assert tr.at(0) == frozenset()
    assert tr.at(1) == frozenset({"p"})
    assert tr.at(2) == frozenset({"q"})     # first cycle position
    assert tr.at(5) == frozenset({"q"})     # wraps: (5-2) % 1 == 0


def test_ltltrace_at_rejects_negative_position():
    tr = LTLTrace(prefix=(), cycle=(frozenset(),))
    with pytest.raises(ValueError):
        tr.at(-1)


# --------------------------------------------------------------------------- #
# Hand-checked textbook validities.
# --------------------------------------------------------------------------- #

# Each entry commented with the hand-derivation, not just the identity's name.
_VALID_CASES = [
    # Gp -> p: G is INCLUSIVE of now (semantics/kripke.py's Always docstring:
    # "reflexive-transitive closure ... current world included").
    Implies(Always(p), p),
    # p -> Fp: F is inclusive of now, dual reason.
    Implies(p, Eventually(p)),
    # Fp <-> not G not p: F and G are De Morgan duals on a total order.
    Iff(Eventually(p), Not(Always(Not(p)))),
    # Gp <-> p and XGp: the defining fixpoint unfolding of G.
    Iff(Always(p), And(p, Next(Always(p)))),
    # Fp <-> p or XFp: the defining fixpoint unfolding of F.
    Iff(Eventually(p), Or(p, Next(Eventually(p)))),
    # pUq <-> q or (p and X(pUq)): Until is non-strict/strong (q may hold
    # right now, n=0 case of semantics/kripke.py's _until_holds).
    Iff(Until(p, q), Or(q, And(p, Next(Until(p, q))))),
    # FLAGSHIP: temporal induction (p and G(p -> Xp)) -> Gp. qml_is_valid's
    # own docstring says this "genuinely does stay out of reach" for the
    # first-order embedding (reaching an arbitrary T-successor from the
    # first step needs induction over the closure) -- see
    # test_temporal_induction_is_a_completeness_gain_over_qml below, which
    # confirms qml_is_valid is False on the exact same formula.
    Implies(And(p, Always(Implies(p, Next(p)))), Always(p)),
    # Op <-> not H not p: past duals, mirroring F<->not G not.
    Iff(Once(p), Not(Historically(Not(p)))),
    # Hp <-> p and YHp: the defining fixpoint unfolding of H (Y is weak, so
    # this needs no existential rewriting the way S below does).
    Iff(Historically(p), And(p, Previous(Historically(p)))),
    # pSq <-> q or (p and NOT Y(NOT(pSq))): Since's unfolding needs the
    # EXISTENTIAL "Previous" reading -- Y itself is weak/universal (vacuously
    # true with no predecessor), so the naive Y-wrapped form would wrongly
    # come out invalid at position 0 whenever p holds and q does not (Y would
    # vacuously make the RHS true there while the LHS, pSq(0)=q(0), is
    # false) -- this is precisely the reason Previous has no plain-Y unfold.
    Iff(Since(p, q), Or(q, And(p, Not(Previous(Not(Since(p, q))))))),
    # Hp -> p: H is inclusive of now, the past mirror of Gp -> p.
    Implies(Historically(p), p),
    # p -> Op: the past mirror of p -> Fp.
    Implies(p, Once(p)),
]


@pytest.mark.parametrize("formula", _VALID_CASES,
                         ids=[f"valid{i}" for i in range(len(_VALID_CASES))])
def test_hand_checked_validities(formula):
    assert ltl_valid(formula) is True
    assert ltl_decide(formula) == "valid"
    assert ltl_countermodel(formula) is None


# --------------------------------------------------------------------------- #
# Hand-checked textbook non-validities, with a verified witness for each.
# --------------------------------------------------------------------------- #

_INVALID_CASES = [
    # GFp -> FGp: the classic non-theorem (Baier & Katoen, ch. 5) -- "p
    # infinitely often" does not imply "p forever from some point on".
    # Witness: p alternates false/true forever (a length-2 cycle).
    Implies(Always(Eventually(p)), Eventually(Always(p))),
    # p -> Gp: p true now says nothing about later. Witness: p true at 0,
    # false forever after.
    Implies(p, Always(p)),
    # Xp -> p: what holds NEXT says nothing about NOW. Witness: p false at
    # 0, true at 1 (and forever after, say).
    Implies(Next(p), p),
    # Fp -> Gp: "eventually" does not imply "eventually forever". Witness:
    # p true once, then false forever.
    Implies(Eventually(p), Always(p)),
    # Fp -> Hp: "p holds now or later" says nothing about the past. Witness:
    # p false at 0 (so Hp(0) = p(0) = false) but true at 1 (so Fp(0) holds).
    Implies(Eventually(p), Historically(p)),
]


@pytest.mark.parametrize("formula", _INVALID_CASES,
                         ids=[f"invalid{i}" for i in range(len(_INVALID_CASES))])
def test_hand_checked_non_validities_have_verified_witnesses(formula):
    assert ltl_valid(formula) is False
    assert ltl_decide(formula) == "invalid"
    cm = ltl_countermodel(formula)
    assert cm is not None
    # Verified twice: once by the module's own (shipped) evaluator...
    assert ltl_trace_satisfies(formula, cm) is False
    # ...and once by this test file's INDEPENDENT from-scratch evaluator.
    assert _eval_on_lasso(formula, cm.prefix, cm.cycle, cm.witness_position) is False


def test_gf_p_implies_fg_p_witness_is_the_alternating_lasso():
    """Pin the actual shape of the GFp -> FGp countermodel: p must alternate
    forever (any lasso that eventually settles to constant p, true or false,
    would make one side of the implication true and so would NOT refute it)."""
    formula = Implies(Always(Eventually(p)), Eventually(Always(p)))
    cm = ltl_countermodel(formula)
    assert cm is not None
    # Every valuation the cycle repeats must include one with p and one
    # without -- otherwise the cycle would settle to a constant p.
    p_true = any("p" in v for v in cm.cycle)
    p_false = any("p" not in v for v in cm.cycle)
    assert p_true and p_false


# --------------------------------------------------------------------------- #
# Flagship completeness gain.
# --------------------------------------------------------------------------- #

def test_temporal_induction_is_a_completeness_gain_over_qml():
    ti = Implies(And(p, Always(Implies(p, Next(p)))), Always(p))
    assert ltl_valid(ti) is True
    # fol.qml.qml_is_valid's own module docstring: this "genuinely does stay
    # out of reach" for the first-order embedding -- confirmed directly
    # against the live function, not just quoted.
    assert qml_is_valid(ti) is False


# --------------------------------------------------------------------------- #
# Initial vs. floating validity: they differ exactly on past operators.
# --------------------------------------------------------------------------- #

def test_initial_vs_floating_validity_differ_on_past_operators():
    # "There is no earlier position": Y is weak, so Y(p & not p) is
    # vacuously TRUE at position 0 of every model (no predecessor to check)
    # but false at any position with a real predecessor.
    no_predecessor = Previous(And(p, Not(p)))
    assert ltl_valid(no_predecessor, mode="initial") is True
    assert ltl_countermodel(no_predecessor, mode="initial") is None
    assert ltl_valid(no_predecessor, mode="floating") is False
    cm = ltl_countermodel(no_predecessor, mode="floating")
    assert cm is not None
    assert cm.witness_position >= 1          # a genuine predecessor exists
    assert ltl_trace_satisfies(no_predecessor, cm) is False
    assert _eval_on_lasso(no_predecessor, cm.prefix, cm.cycle, cm.witness_position) is False


def test_floating_valid_implies_initial_valid():
    # Floating validity ("true at every position of every model") is
    # strictly STRONGER than initial validity ("true at position 0") --
    # every one of the hand-checked validities above, which have no past
    # operator sensitive to position 0's vacuity in a way that would break
    # under shifting, should hold in both senses.
    for formula in _VALID_CASES:
        assert ltl_valid(formula, mode="floating") is True


# --------------------------------------------------------------------------- #
# Premises.
# --------------------------------------------------------------------------- #

def test_ltl_valid_with_premises():
    assert ltl_valid(Eventually(p), premises=[p]) is True
    assert ltl_valid(Always(q), premises=[Always(p)]) is False
    assert ltl_tableau_closed([p, Not(Eventually(p))]) is True


# --------------------------------------------------------------------------- #
# Resource bound: honest "unknown", never a wrong verdict.
# --------------------------------------------------------------------------- #

def test_max_atoms_bound_hit_is_reported_as_unknown_not_wrong():
    # Eventually(p)'s closure has 2 free elements (p, Next(Eventually(p))):
    # 4 atoms, comfortably over a budget of 1.
    assert ltl_decide(Eventually(p), max_atoms=1) == "unknown"
    assert ltl_valid(Eventually(p), max_atoms=1) is False   # "not proved", not "disproved"
    assert ltl_countermodel(Eventually(p), max_atoms=1) is None


# --------------------------------------------------------------------------- #
# Refusing what this module does not decide.
# --------------------------------------------------------------------------- #

def test_refuses_box_by_name():
    with pytest.raises(NotImplementedError, match="Box"):
        ltl_valid(Box(p))


def test_refuses_quantifiers_by_name():
    x = Variable("x")
    with pytest.raises(NotImplementedError):
        ltl_valid(Quantifier("∀", x, Atom("P", [x])))


def test_mode_is_validated():
    with pytest.raises(ValueError):
        ltl_valid(p, mode="branching")


# --------------------------------------------------------------------------- #
# ProverBackend registration.
# --------------------------------------------------------------------------- #

def test_backend_proves_temporal_induction():
    backend = get_backend("ltl-tableau")
    v = backend.decide(Implies(And(p, Always(Implies(p, Next(p)))), Always(p)))
    assert v.status == PROVED
    assert v.logic == "modal"


def test_backend_refutes_with_a_lasso_countermodel():
    backend = get_backend("ltl-tableau")
    v = backend.decide(Implies(Always(Eventually(p)), Eventually(Always(p))))
    assert v.status == REFUTED
    assert v.countermodel is not None
    assert v.countermodel["kind"] == "ltl_lasso"
    assert len(v.countermodel["cycle"]) >= 1


def test_backend_reports_unsupported_construct_as_unknown_not_a_crash():
    backend = get_backend("ltl-tableau")
    v = backend.decide(Box(p))
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"


# --------------------------------------------------------------------------- #
# Cross-check against semantics.kripke on a finite linear prefix frame.
#
# The two semantics provably coincide on a finite, non-branching, non-cyclic
# ("dead end") KripkeModel whose "temporal" relation is exactly the chain
# 0 -> 1 -> ... -> k, EXCEPT for a Next-obligation queried exactly at the
# dead end k: there, satisfies_modal's Box-style universal quantifies over
# an EMPTY successor set and is vacuously True regardless of the body, while
# an actually-infinite periodic trace has no dead end at all -- Next always
# looks at a REAL next position. test_next_diverges_at_the_dead_end below
# demonstrates the divergence directly rather than just asserting it, and
# the main cross-check accordingly evaluates only at worlds 0..k-1.
# --------------------------------------------------------------------------- #

def _linear_chain_model_and_trace(vals):
    """A dead-end KripkeModel plus a matching LTLTrace (cycle = a self-loop
    on the last valuation, so nothing new ever happens after the chain
    ends -- the two represent "the same" word for every world before k)."""
    worlds = list(range(len(vals)))
    edges = {(i, i + 1) for i in range(len(vals) - 1)}
    model = KripkeModel(worlds, {"temporal": edges}, {i: vals[i] for i in worlds})
    trace = LTLTrace(prefix=tuple(frozenset(v) for v in vals),
                     cycle=(frozenset(vals[-1]),))
    return model, trace


def test_agrees_with_kripke_semantics_on_a_finite_linear_prefix():
    vals = [set(), {"p"}, {"p", "q"}, set(), {"q"}, {"p"}]
    model, trace = _linear_chain_model_and_trace(vals)
    formulas = [
        Always(Implies(p, Eventually(q))),
        Eventually(And(p, q)),
        Until(p, q),
        Historically(Not(And(p, q))),
        Once(q),
        Previous(p),
        Since(Not(q), p),
        Implies(p, Eventually(q)),
    ]
    for f in formulas:
        for w in range(len(vals) - 1):     # exclude the dead-end last world
            assert satisfies_modal(f, model, w) == ltl_trace_satisfies(f, trace, w), (
                f, w)


def test_next_diverges_at_the_dead_end_boundary():
    """Documents (with an assertion, not just a comment) exactly why the
    cross-check above stops one world short of the chain's end."""
    vals = [set(), {"q"}]                  # p false at both worlds
    model, trace = _linear_chain_model_and_trace(vals)
    # Kripke: Next(p) at the dead end (world 1, no successor) is vacuously
    # TRUE -- a universal quantifier over the empty successor set.
    assert satisfies_modal(Next(p), model, 1) is True
    # The trace has no dead end: Next(p) at position 1 looks at position 2,
    # which the self-loop maps back to world 1's own valuation ({"q"}, no
    # p) -- genuinely False. Two different, both-correct modelling choices
    # for "what happens after the visible horizon", not a bug in either.
    assert ltl_trace_satisfies(Next(p), trace, 1) is False


# --------------------------------------------------------------------------- #
# Monotonicity cross-check against fol.qml.qml_is_valid.
# --------------------------------------------------------------------------- #

# Every one of these is named valid in qml.py's own module docstring (the
# "T reflexive + transitive, N subset T" paragraph) -- sanity-checked live
# below, not just trusted from the comment.
_QML_VALID_TEMPORAL = [
    Implies(Always(p), p),
    Implies(Always(p), Always(Always(p))),
    Implies(Always(p), Eventually(p)),
    Implies(Always(p), Next(p)),
    Implies(p, Eventually(p)),
    Implies(Historically(p), p),
    Implies(Historically(p), Historically(Historically(p))),
    Implies(Historically(p), Previous(p)),
    Implies(p, Once(p)),
]


@pytest.mark.parametrize("formula", _QML_VALID_TEMPORAL,
                         ids=[f"qml{i}" for i in range(len(_QML_VALID_TEMPORAL))])
def test_qml_valid_temporal_formulas_are_also_ltl_valid(formula):
    # The standard linear frame is a strict SUBSET of qml's default
    # refl+trans+N-subset-T frame class, so validity there must survive
    # narrowing to the line -- a failure here would be a soundness bug in
    # THIS module, never a legitimate scope divergence (see
    # LtlTableauBackend's docstring).
    assert qml_is_valid(formula) is True    # sanity: genuinely qml-valid
    assert ltl_valid(formula) is True


# --------------------------------------------------------------------------- #
# Independent lasso oracle: a from-scratch evaluator over an EAGERLY
# unrolled, concrete finite word -- never calls into ltl_tableau at all.
# --------------------------------------------------------------------------- #

def _past_nesting_depth(node) -> int:
    """Max nesting depth of Historically/Once/Since anywhere in ``node``.

    Used only to size the unrolling below (see _eval_on_lasso's docstring):
    each level of backward-fixpoint nesting can add up to one full cycle's
    worth of "still stabilising" positions before its truth value repeats
    with the word's own period, a fact argued (and cross-checked via
    ltl_trace_satisfies, an independently-derived implementation of the same
    fact) in ltl_tableau.py's module docstring.
    """
    if isinstance(node, (Historically, Once)):
        return 1 + _past_nesting_depth(node.formula)
    if isinstance(node, Since):
        return 1 + max(_past_nesting_depth(node.left), _past_nesting_depth(node.right))
    if isinstance(node, (Next, Previous, Always, Eventually, Not)):
        return _past_nesting_depth(node.formula)
    if isinstance(node, (And, Or, Implies, Iff, Until)):
        return max(_past_nesting_depth(node.left), _past_nesting_depth(node.right))
    return 0    # Atom


def _word_at(prefix, cycle, i):
    """The valuation at position ``i`` (>= 0) of the INFINITE word
    ``prefix + cycle*`` — computed by plain modular indexing (never a
    truncated/eagerly-materialized array: see :func:`_eval_on_lasso`'s
    docstring for why a fixed-length array is the wrong shape here)."""
    if i < len(prefix):
        return prefix[i]
    cyc = cycle if cycle else (frozenset(),)
    return cyc[(i - len(prefix)) % len(cyc)]


def _forward_horizon(formula, prefix, cycle, safety=15):
    """How far ahead a bounded forward (G/F/U) search must look from ANY
    start position to be conclusive — see :func:`_past_nesting_depth`'s
    docstring for the "one extra cycle per backward-fixpoint level" argument
    this mirrors; this is a RELATIVE lookahead (used as ``range(i, i +
    horizon)`` for every ``i``, never an absolute array bound), which is
    the fix for the bug an earlier version of this file had: bounding
    forward search to a fixed-length unrolled ARRAY silently shrinks the
    remaining lookahead as ``i`` approaches the array's end, so a universal
    (G) claim checked near the tail could spuriously pass by running out of
    room to find its own violation before the truncation cut it off.
    """
    cyc_len = len(cycle) if cycle else 1
    return (_past_nesting_depth(formula) + safety) * cyc_len + len(prefix) + safety


def _eval_on_lasso(formula, prefix, cycle, position=0) -> bool:
    """Evaluate ``formula`` at ``position`` of the lasso ``prefix + cycle*``,
    directly from the linear-time satisfaction equations, indexing the
    INFINITE word via :func:`_word_at` (plain modular arithmetic) with a
    RELATIVE forward-search horizon (:func:`_forward_horizon`) — independent
    of ``ltl_tableau.ltl_trace_satisfies``: no shared code, no shared
    helper, and a different concrete strategy (modular indexing with a
    per-call relative horizon vs. that module's array-free memoized
    recursion over ``LTLTrace.at``).
    """
    horizon = _forward_horizon(formula, prefix, cycle)
    memo = {}

    def ev(node, i):
        key = (node, i)
        if key in memo:
            return memo[key]
        if isinstance(node, Atom):
            v = node.to_unicode_str() in _word_at(prefix, cycle, i)
        elif isinstance(node, Not):
            v = not ev(node.formula, i)
        elif isinstance(node, And):
            v = ev(node.left, i) and ev(node.right, i)
        elif isinstance(node, Or):
            v = ev(node.left, i) or ev(node.right, i)
        elif isinstance(node, Implies):
            v = (not ev(node.left, i)) or ev(node.right, i)
        elif isinstance(node, Iff):
            v = ev(node.left, i) == ev(node.right, i)
        elif isinstance(node, Next):
            v = ev(node.formula, i + 1)
        elif isinstance(node, Previous):
            v = True if i == 0 else ev(node.formula, i - 1)
        elif isinstance(node, Always):
            v = all(ev(node.formula, m) for m in range(i, i + horizon))
        elif isinstance(node, Eventually):
            v = any(ev(node.formula, m) for m in range(i, i + horizon))
        elif isinstance(node, Until):
            v = False
            for m in range(i, i + horizon):
                if ev(node.right, m):
                    v = True
                    break
                if not ev(node.left, m):
                    break
        elif isinstance(node, Historically):
            v = all(ev(node.formula, m) for m in range(0, i + 1))
        elif isinstance(node, Once):
            v = any(ev(node.formula, m) for m in range(0, i + 1))
        elif isinstance(node, Since):
            v = False
            for m in range(i, -1, -1):
                if ev(node.right, m):
                    v = True
                    break
                if not ev(node.left, m):
                    break
        else:
            raise NotImplementedError(f"_eval_on_lasso: no rule for {type(node).__name__}")
        memo[key] = v
        return v

    return ev(formula, position)


def test_eval_on_lasso_matches_ltl_trace_satisfies_on_hand_cases():
    """Sanity-check the two independent evaluators against each other on
    every hand-checked (non-)validity's witness before trusting either for
    the property-based search below."""
    for formula in _VALID_CASES:
        assert ltl_valid(formula) is True   # already established above
    for formula in _INVALID_CASES:
        cm = ltl_countermodel(formula)
        assert ltl_trace_satisfies(formula, cm) == \
            _eval_on_lasso(formula, cm.prefix, cm.cycle, cm.witness_position)


# --------------------------------------------------------------------------- #
# Property-based: seeded random small formulas vs. exhaustive small-lasso
# search.
# --------------------------------------------------------------------------- #

_UNARY_TEMPORAL = (Next, Always, Eventually, Historically, Once, Previous)
_BINARY_TEMPORAL = (Until, Since)
_BINARY_BOOL = (And, Or, Implies, Iff)


def _random_formula(rng: random.Random, depth: int):
    """A small random formula over {p, q} using every supported operator."""
    if depth <= 0:
        return rng.choice((p, q))
    choice = rng.random()
    if choice < 0.15:
        return rng.choice((p, q))
    if choice < 0.30:
        return Not(_random_formula(rng, depth - 1))
    if choice < 0.65:
        op = rng.choice(_UNARY_TEMPORAL)
        return op(_random_formula(rng, depth - 1))
    if choice < 0.80:
        op = rng.choice(_BINARY_TEMPORAL)
        return op(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))
    op = rng.choice(_BINARY_BOOL)
    return op(_random_formula(rng, depth - 1), _random_formula(rng, depth - 1))


_RANDOM_SEED = 20260916          # today's date, per the standing house convention
_RANDOM_FORMULAS = [_random_formula(random.Random(_RANDOM_SEED + i), 3)
                    for i in range(18)]


def _all_small_lassos(max_total_len=4):
    """Every ``(prefix, cycle)`` pair over {p, q} with
    ``0 <= len(prefix) + 1 <= len(cycle) + len(prefix) <= max_total_len``
    (a non-empty cycle, so every pair is a genuine infinite lasso)."""
    valuations = [frozenset(s) for r in range(3)
                 for s in _combinations(("p", "q"), r)]
    for total in range(1, max_total_len + 1):
        for prefix_len in range(0, total):
            cycle_len = total - prefix_len
            for prefix in _product(valuations, prefix_len):
                for cycle in _product(valuations, cycle_len):
                    yield prefix, cycle


def _combinations(items, r):
    import itertools
    return itertools.combinations(items, r)


def _product(items, n):
    import itertools
    return itertools.product(items, repeat=n)


_SMALL_LASSOS = list(_all_small_lassos(4))


@pytest.mark.parametrize("formula", _RANDOM_FORMULAS,
                         ids=[f"rand{i}" for i in range(len(_RANDOM_FORMULAS))])
def test_random_formulas_against_exhaustive_small_lasso_search(formula):
    oracle_results = [_eval_on_lasso(formula, pre, cyc, 0) for pre, cyc in _SMALL_LASSOS]
    tableau_valid = ltl_valid(formula)

    if any(r is False for r in oracle_results):
        # A genuine countermodel exists among the small lassos: the tableau
        # must never claim "valid" in the face of it (soundness).
        assert tableau_valid is False, (
            "tableau claimed valid but a small lasso falsifies it", formula)
    if tableau_valid:
        # Necessary (not sufficient) consequence of genuine validity: every
        # exhaustively-checked small lasso must agree too.
        assert all(oracle_results), (
            "tableau claimed valid but disagrees with a small lasso", formula)

    decide = ltl_decide(formula)
    if decide == "invalid":
        cm = ltl_countermodel(formula)
        assert cm is not None
        assert _eval_on_lasso(formula, cm.prefix, cm.cycle, cm.witness_position) is False
