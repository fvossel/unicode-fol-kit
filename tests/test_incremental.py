"""Tests for ``unicode_fol_kit.atp.incremental`` (roadmap K2).

:class:`~unicode_fol_kit.atp.incremental.IncrementalSession` keeps ONE
persistent ``z3.Solver`` alive across many ``decide()`` calls against a
premise set that only grows/shrinks via native Z3 push/pop, instead of
rebuilding a fresh ``Solver`` (and re-asserting every premise) per call the
way :class:`~unicode_fol_kit.atp.protocol.Z3Backend` does. Everything here is
checked against that STATELESS route — an independent second decision
procedure, not a self-check — via :func:`_agrees_with_stateless`, which every
test in the differential batteries below routes through.

Coverage, matching the K2 test_oracle:

* a hand-picked battery spanning propositional/quantified FOL, equality,
  function terms and many-sorted formulas, each with a HAND-WORKED expected
  PROVED/REFUTED verdict (see the comment on each case);
* a seeded random battery over the same fragment;
* the many-sorted non-emptiness soundness case the module docstring itself
  is built around ((∀x:S P(x)) → ∃x:S P(x)), which the OLD polarity-blind
  ``to_fol`` relativisation alone gets wrong without the axiom;
* push/pop correctness: an interleaved assert/decide/retract/decide sequence
  where the second ``decide(g1)`` must reproduce the very first one exactly;
* retract() past the base premises raising, never silently no-op/mis-popping;
* a timeout is reported UNKNOWN, never REFUTED (deterministically forced by
  monkeypatching the underlying solver, since a genuinely Z3-hard formula at
  this fragment's size is not reproducible on demand);
* a scope-depth (push/pop) balance assertion after every ``decide()`` call in
  every battery below, via the same shared helper;
* for a REFUTED propositional case, the returned countermodel is
  independently re-checked with the kit's own two-valued Tarski evaluator
  (``semantics.tarski.satisfies``) rather than trusting Z3's own model dump
  twice;
* agreement with ``atp.z3_models.is_valid``/``get_model`` — a THIRD,
  differently-shaped route to the same Z3 answer.
"""

import random as _random

import pytest
import z3

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.incremental import IncrementalSession
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, Z3Backend
from unicode_fol_kit.atp.z3_models import get_model, is_satisfiable, is_valid
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Implies, Not, Or, Quantifier, Variable
from unicode_fol_kit.semantics.tarski import Structure, satisfies

FOL = MSFLParser()
MSFOL = MSFLParser(many_sorted=True)
LINEAR = MSFLParser(linear=True)

_Z3 = Z3Backend()


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

def _fold(goal, premises):
    """``(∧ premises) → goal`` — the same implication Z3Backend's modal/qml
    helpers and z3_models' single-formula routes decide, for the
    is_valid/get_model cross-check below."""
    premises = list(premises)
    if not premises:
        return goal
    conj = premises[0]
    for p in premises[1:]:
        conj = And(conj, p)
    return Implies(conj, goal)


def _agrees_with_stateless(session, goal, premises, *, timeout=None):
    """Decide ``goal`` on ``session`` and assert it agrees with a FRESH
    ``Z3Backend().decide(goal, premises)`` call — the independent second
    route the K2 test_oracle names — and that push/pop stayed balanced.

    ``premises`` must be exactly ``session``'s current premise set (its
    caller's job, since the session cannot tell a stale caller-side copy
    from a live one).
    """
    depth_before = session.scope_depth
    kwargs = {} if timeout is None else {"timeout": timeout}
    v = session.decide(goal, **kwargs)
    assert session.scope_depth == depth_before, (
        "IncrementalSession.decide must leave scope_depth unchanged")
    ref = _Z3.decide(goal, list(premises), **kwargs)
    assert v.status == ref.status, (
        f"disagreement on {goal.to_unicode_str()} given "
        f"{[p.to_unicode_str() for p in premises]}: "
        f"session={v.status!r} stateless={ref.status!r}")
    return v, ref


def _propositional_atom_names(*formulas):
    names = []
    for f in formulas:
        for n in f.walk():
            if isinstance(n, Atom) and not n.args and n.predicate not in names:
                names.append(n.predicate)
    return names


# ---------------------------------------------------------------------------
# Hand-picked battery: propositional, quantified FOL, equality, functions,
# many-sorted -- each expected status worked out by hand (see the comment).
# ---------------------------------------------------------------------------

_a, _b = Constant("a"), Constant("b")

_HAND_PICKED = [
    # Modus ponens: P → Q, P ⊢ Q -- textbook valid.
    ("modus_ponens", ["P → Q", "P"], "Q", PROVED),
    # Disjunctive "syllogism" WITHOUT the negated disjunct is not valid: Q
    # could be the true disjunct while P is false -- Z3's own countermodel.
    ("disjunction_does_not_entail_a_disjunct", ["P ∨ Q"], "P", REFUTED),
    # Barbara syllogism instantiated: ∀x(Human(x)→Mortal(x)), Human(socrates)
    # ⊢ Mortal(socrates) -- universal instantiation, valid.
    ("barbara_instantiated",
     ["∀x (Human(x) → Mortal(x))", "Human(socrates)"], "Mortal(socrates)", PROVED),
    # A single witness does not license universal generalisation: P(a) does
    # NOT entail ∀x P(x) (some other individual b need not be P) -- classic
    # non-entailment, refuted.
    ("witness_does_not_generalise", ["P(a)"], "∀x P(x)", REFUTED),
    # Leibniz substitution via equality: a = b, P(a) ⊢ P(b) -- valid.
    ("equality_substitution", ["a = b", "P(a)"], "P(b)", PROVED),
    # Nothing forces two distinct constants to denote the same individual in
    # an uninterpreted sort -- a = b is NOT valid on its own (Z3 can assign
    # a and b distinct domain elements), refuted.
    ("distinct_constants_not_forced_equal", [], "a = b", REFUTED),
    # Function congruence + substitution: f(a) = b, P(f(a)) ⊢ P(b) -- valid.
    ("function_congruence_substitution",
     ["f(a) = b", "P(f(a))"], "P(b)", PROVED),
    # P(f(a)) does not entail P(f(b)): f(a) and f(b) need not coincide when
    # a ≠ b is not excluded -- refuted.
    ("distinct_function_applications_not_forced_equal",
     ["P(f(a))"], "P(f(b))", REFUTED),
]


@pytest.mark.parametrize("name,prem_strs,goal_str,expected", _HAND_PICKED,
                         ids=[c[0] for c in _HAND_PICKED])
def test_hand_picked_battery_agrees_with_stateless(name, prem_strs, goal_str, expected):
    premises = [FOL.parse(s) for s in prem_strs]
    goal = FOL.parse(goal_str)
    session = IncrementalSession(premises)
    v, ref = _agrees_with_stateless(session, goal, premises)
    assert v.status == expected, f"{name}: expected {expected}, got {v.status}"
    assert ref.status == expected, f"{name}: stateless oracle itself disagrees (test bug)"


# ---------------------------------------------------------------------------
# Many-sorted (MSFOL): the exact motivating case from the module docstring,
# plus a REFUTED many-sorted case with premises added incrementally.
# ---------------------------------------------------------------------------

def test_sorted_forall_implies_exists_needs_the_nonemptiness_axiom():
    """(∀x:Human Mortal(x)) → ∃x:Human Mortal(x)) is valid ONLY because
    MSFOL's convention makes every sort non-empty -- see the incremental
    module's docstring and the classical-reasoning guide's many-sorted
    section. Without asserting that axiom the same way Z3Backend does, a
    solver is free to make Human's extension empty and REFUTE this."""
    goal = MSFOL.parse("(∀x:Human Mortal(x)) → ∃x:Human Mortal(x)")
    session = IncrementalSession([])
    v, ref = _agrees_with_stateless(session, goal, [])
    assert v.status == PROVED
    assert ref.status == PROVED


def test_sorted_premises_added_incrementally_still_get_the_axiom():
    """∀x:Dog Bark(x) ⊢ ∃x:Dog Bark(x) -- valid because Dog is non-empty --
    checked with the premise added via assert_premise (not the
    constructor), so the axiom must be recomputed from the LIVE premise
    stack, not just the constructor's base set."""
    premise = MSFOL.parse("∀x:Dog Bark(x)")
    goal = MSFOL.parse("∃x:Dog Bark(x)")
    session = IncrementalSession([])
    session.assert_premise(premise)
    v, ref = _agrees_with_stateless(session, goal, [premise])
    assert v.status == PROVED
    assert ref.status == PROVED


def test_sorted_two_sorts_refuted_countermodel_agrees():
    """∀x:Dog Bark(x), ∀x:Human ¬Bark(x) ⊬ ∃x:Human Bark(x) -- Dogs bark,
    Humans don't, so no Human barks either; refuted, with a legal
    (non-empty-sort) countermodel."""
    p1 = MSFOL.parse("∀x:Dog Bark(x)")
    p2 = MSFOL.parse("∀x:Human ¬Bark(x)")
    goal = MSFOL.parse("∃x:Human Bark(x)")
    session = IncrementalSession([p1])
    session.assert_premise(p2)
    v, ref = _agrees_with_stateless(session, goal, [p1, p2])
    assert v.status == REFUTED
    assert ref.status == REFUTED
    assert v.countermodel["kind"] == "z3_model"


# ---------------------------------------------------------------------------
# Seeded random battery -- propositional and quantified FOL.
# ---------------------------------------------------------------------------

_PROP_ATOMS = [Atom(name, ()) for name in ("P", "Q", "R")]
_UNARY_PREDS = ["P", "Q"]
_CONSTS = [Constant("a"), Constant("b")]


def _random_prop(depth, rng):
    if depth <= 0 or rng.random() < 0.35:
        atom = rng.choice(_PROP_ATOMS)
        return Not(atom) if rng.random() < 0.4 else atom
    op = rng.choice([And, "or", Implies, "not"])
    if op == "not":
        return Not(_random_prop(depth - 1, rng))
    if op == "or":
        return Or(_random_prop(depth - 1, rng), _random_prop(depth - 1, rng))
    return op(_random_prop(depth - 1, rng), _random_prop(depth - 1, rng))


def _random_term(bound_vars, rng):
    if bound_vars and rng.random() < 0.6:
        return Variable(rng.choice(bound_vars))
    return rng.choice(_CONSTS)


def _random_fol(depth, bound_vars, rng):
    """A random closed FOL sentence over unary P/Q, constants a/b, and
    quantifiers binding fresh variables -- bounded shallow so Z3 always
    decides it well within the default timeout (no genuine hardness here;
    only the hand-picked/timeout tests exercise UNKNOWN)."""
    if depth <= 0 or rng.random() < 0.3:
        pred = rng.choice(_UNARY_PREDS)
        return Atom(pred, (_random_term(bound_vars, rng),))
    choice = rng.random()
    if choice < 0.25 and depth > 1:
        var = f"v{len(bound_vars)}"
        qtype = rng.choice(["∀", "∃"])
        body = _random_fol(depth - 1, bound_vars + [var], rng)
        return Quantifier(qtype, Variable(var), body)
    if choice < 0.45:
        return Not(_random_fol(depth - 1, bound_vars, rng))
    if choice < 0.65:
        return And(_random_fol(depth - 1, bound_vars, rng),
                   _random_fol(depth - 1, bound_vars, rng))
    if choice < 0.85:
        return Or(_random_fol(depth - 1, bound_vars, rng),
                 _random_fol(depth - 1, bound_vars, rng))
    return Implies(_random_fol(depth - 1, bound_vars, rng),
                   _random_fol(depth - 1, bound_vars, rng))


def test_random_propositional_battery_agrees_with_stateless():
    rng = _random.Random(20260913)
    proved = refuted = 0
    for _ in range(120):
        k = rng.randint(0, 2)
        premises = [_random_prop(rng.randint(1, 2), rng) for _ in range(k)]
        goal = _random_prop(rng.randint(1, 2), rng)
        session = IncrementalSession(premises)
        v, ref = _agrees_with_stateless(session, goal, premises)
        proved += int(v.status == PROVED)
        refuted += int(v.status == REFUTED)
    # Sanity: the seeded batch actually exercised both definitive outcomes.
    assert proved > 0 and refuted > 0


def test_random_quantified_battery_agrees_with_stateless():
    rng = _random.Random(987123456)
    proved = refuted = 0
    for _ in range(80):
        k = rng.randint(0, 2)
        premises = [_random_fol(rng.randint(1, 2), [], rng) for _ in range(k)]
        goal = _random_fol(rng.randint(1, 2), [], rng)
        session = IncrementalSession(premises)
        v, ref = _agrees_with_stateless(session, goal, premises)
        proved += int(v.status == PROVED)
        refuted += int(v.status == REFUTED)
    assert proved > 0 and refuted > 0


def test_random_battery_grown_incrementally_via_assert_premise_agrees():
    """Same random quantified generator, but every premise goes through
    assert_premise/retract instead of the constructor -- exercising the
    push/pop machinery itself, not just decide()'s own translation."""
    rng = _random.Random(13)
    for _ in range(40):
        k = rng.randint(0, 3)
        premises = [_random_fol(rng.randint(1, 2), [], rng) for _ in range(k)]
        goal = _random_fol(rng.randint(1, 2), [], rng)
        session = IncrementalSession([])
        for p in premises:
            session.assert_premise(p)
        # Retract and re-assert a random prefix, to also walk the LIFO stack
        # before the query that actually matters.
        n_retract = rng.randint(0, len(premises))
        removed = [session.retract() for _ in range(n_retract)]
        for p in reversed(removed):
            session.assert_premise(p)
        assert session.premises == tuple(premises)
        _agrees_with_stateless(session, goal, premises)


# ---------------------------------------------------------------------------
# push/pop correctness: retract() truly returns to the prior solver state.
# ---------------------------------------------------------------------------

def test_retract_returns_to_prior_solver_state():
    prem_base = FOL.parse("∀x (P(x) → Q(x))")
    p1 = FOL.parse("P(a)")
    p2 = FOL.parse("R(b) ∨ ¬R(b)")   # an unrelated tautology, just noise
    g1 = FOL.parse("Q(a)")
    g2 = FOL.parse("R(b)")

    session = IncrementalSession([prem_base])
    session.assert_premise(p1)
    v_g1_first, _ = _agrees_with_stateless(session, g1, [prem_base, p1])
    assert v_g1_first.status == PROVED

    session.assert_premise(p2)
    _agrees_with_stateless(session, g2, [prem_base, p1, p2])

    removed = session.retract()
    assert removed == p2
    assert session.premises == (prem_base, p1)

    v_g1_again, _ = _agrees_with_stateless(session, g1, [prem_base, p1])
    # Solver state is now byte-for-byte what it was for the very FIRST
    # decide(g1) call -- same assertions, same fixed random_seed -- so the
    # verdict must match exactly, not merely agree on .status.
    assert v_g1_again.status == v_g1_first.status == PROVED
    assert v_g1_again.reason == v_g1_first.reason
    assert v_g1_again.countermodel == v_g1_first.countermodel


def test_retract_past_base_premises_raises():
    session = IncrementalSession([FOL.parse("P")])
    with pytest.raises(ValueError, match="retract"):
        session.retract()

    session.assert_premise(FOL.parse("Q"))
    assert session.retract() == FOL.parse("Q")   # fine: undoes assert_premise

    with pytest.raises(ValueError, match="retract"):
        session.retract()   # base premise "P" is never reachable


def test_retract_is_strictly_lifo_one_at_a_time():
    session = IncrementalSession([])
    p1, p2, p3 = FOL.parse("P"), FOL.parse("Q"), FOL.parse("R")
    session.assert_premise(p1)
    session.assert_premise(p2)
    session.assert_premise(p3)
    assert session.retract() == p3
    assert session.retract() == p2
    assert session.premises == (p1,)
    assert session.retract() == p1
    with pytest.raises(ValueError):
        session.retract()


# ---------------------------------------------------------------------------
# Unsupported fragments: refused loudly, never approximated, never a
# half-pushed scope.
# ---------------------------------------------------------------------------

def test_decide_on_unsupported_fragment_is_unknown_and_balances_scope():
    session = IncrementalSession([])
    depth0 = session.scope_depth
    goal = LINEAR.parse("A ⊗ B")
    v = session.decide(goal)
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"
    assert session.scope_depth == depth0


def test_constructor_refuses_unsupported_base_premise_loudly():
    linear_premise = LINEAR.parse("A ⊗ B")
    with pytest.raises(NotImplementedError):
        IncrementalSession([linear_premise])


def test_assert_premise_refuses_unsupported_premise_without_half_pushing():
    session = IncrementalSession([])
    depth0 = session.scope_depth
    linear_premise = LINEAR.parse("A ⊗ B")
    with pytest.raises(NotImplementedError):
        session.assert_premise(linear_premise)
    # No push must have happened -- a failed translation leaves no trace.
    assert session.scope_depth == depth0
    assert session.premises == ()


# ---------------------------------------------------------------------------
# A timeout is UNKNOWN, never REFUTED -- deterministically forced.
# ---------------------------------------------------------------------------

def test_timeout_is_unknown_never_refuted(monkeypatch):
    session = IncrementalSession([])
    goal = FOL.parse("P ∨ ¬P")
    depth0 = session.scope_depth
    monkeypatch.setattr(session._solver, "check", lambda *a, **k: z3.unknown)
    monkeypatch.setattr(session._solver, "reason_unknown", lambda: "timeout, canceled")
    v = session.decide(goal)
    assert v.status == UNKNOWN
    assert v.reason == "timeout"
    assert session.scope_depth == depth0


def test_unknown_without_timeout_wording_is_reported_incomplete(monkeypatch):
    session = IncrementalSession([])
    goal = FOL.parse("P ∨ ¬P")
    monkeypatch.setattr(session._solver, "check", lambda *a, **k: z3.unknown)
    monkeypatch.setattr(session._solver, "reason_unknown",
                        lambda: "smt tactic failed to show goal")
    v = session.decide(goal)
    assert v.status == UNKNOWN
    assert v.reason == "incomplete"


def test_per_call_timeout_override_restores_afterward():
    session = IncrementalSession([], timeout=10000)
    seen = []
    original_set = session._solver.set

    def spy(name, value):
        seen.append((name, value))
        return original_set(name, value)

    session._solver.set = spy
    goal = FOL.parse("P ∨ ¬P")

    session.decide(goal, timeout=50)
    assert ("timeout", 50) in seen
    assert seen[-1] == ("timeout", 10000)   # restored to the constructor's value

    seen.clear()
    session.decide(goal)   # no override this time
    assert seen == []      # decide() must not touch "timeout" at all when not asked


# ---------------------------------------------------------------------------
# Independent (non-Z3) verification of a REFUTED countermodel, and agreement
# with atp.z3_models' single-formula routes.
# ---------------------------------------------------------------------------

def test_refuted_countermodel_independently_verified_via_tarski_structure():
    premises = [FOL.parse("P ∨ Q")]
    goal = FOL.parse("P")
    session = IncrementalSession(premises)
    v = session.decide(goal)
    assert v.status == REFUTED

    assignment = v.countermodel["assignment"]
    names = _propositional_atom_names(goal, *premises)
    predicates = {(name, 0): assignment[name] == "True" for name in names}
    structure = Structure(domain=[0], predicates=predicates)

    # Independently, via the kit's own two-valued Tarski evaluator (never
    # trusting Z3's own model dump twice): the countermodel must satisfy
    # every premise while falsifying the goal.
    for p in premises:
        assert satisfies(p, structure) is True
    assert satisfies(goal, structure) is False


@pytest.mark.parametrize("prem_strs,goal_str,expected", [
    ([], "P ∨ ¬P", PROVED),
    (["∀x (Human(x) → Mortal(x))", "Human(socrates)"], "Mortal(socrates)", PROVED),
    (["P(a)"], "∀x P(x)", REFUTED),
])
def test_session_status_agrees_with_z3_models_is_valid_and_get_model(prem_strs, goal_str, expected):
    premises = [FOL.parse(s) for s in prem_strs]
    goal = FOL.parse(goal_str)
    session = IncrementalSession(premises)
    v = session.decide(goal)
    assert v.status == expected

    implication = _fold(goal, premises)
    assert is_valid(implication) is (expected == PROVED)
    if expected == REFUTED:
        assert is_satisfiable(Not(implication)) is True
        assert get_model(Not(implication)) is not None


# ---------------------------------------------------------------------------
# Basic construction / state-inspection sanity checks.
# ---------------------------------------------------------------------------

def test_premises_property_reflects_base_then_pushed_order():
    base = [FOL.parse("P"), FOL.parse("Q")]
    session = IncrementalSession(base)
    assert session.premises == tuple(base)
    extra = FOL.parse("R")
    session.assert_premise(extra)
    assert session.premises == (base[0], base[1], extra)


def test_scope_depth_starts_at_zero_and_tracks_assert_premise():
    session = IncrementalSession([FOL.parse("P")])   # base premise: no scope
    assert session.scope_depth == 0
    session.assert_premise(FOL.parse("Q"))
    assert session.scope_depth == 1
    session.assert_premise(FOL.parse("R"))
    assert session.scope_depth == 2
    session.retract()
    assert session.scope_depth == 1


def test_constructor_random_seed_makes_countermodels_reproducible():
    premises = [FOL.parse("P ∨ Q")]
    goal = FOL.parse("P")
    v1 = IncrementalSession(premises, random_seed=42).decide(goal)
    v2 = IncrementalSession(premises, random_seed=42).decide(goal)
    assert v1.countermodel == v2.countermodel
