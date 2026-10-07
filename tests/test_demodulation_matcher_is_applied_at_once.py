"""The matcher of a demodulation is applied in ONE simultaneous step: the prover and both proof checkers.

A demodulation rewrites a subterm ``s`` of a clause with the unit equation ``l = r`` when ``l`` one-sidedly
MATCHES ``s``: the equation's variables bind to subterms of the clause, and the clause's own variables are held
fixed. The rule and the clause are not standardized apart (a prover numbers the variables of every clause from
``X0``), so an image of the matcher can be spelled like a variable the matcher binds. The images are terms of the
CLAUSE and are never looked up again; reading them as the equation's variables is wrong.

The rule is ``f(x, y) = g(x)`` (weight 3 against 2, so ``f(x, y) → g(x)`` strictly decreases).

* (A) ``P(f(y, z)) ∨ Q(y)``. The matcher is ``{x: y, y: z}``; the instance of the rule is ``f(y, z) = g(y)``, so
  the right result is ``P(g(y)) ∨ Q(y)``. Following ``x → y → z`` reads ``g(x)`` as ``g(z)`` and gives
  ``P(g(z)) ∨ Q(y)``, which does NOT follow. Countermodel (written out below and checked by enumeration):
  the universe {0, 1}, ``f(u, v) = u``, ``g(u) = u`` (so the equation holds), ``P`` = {0}, ``Q`` = {1}. The
  clause ``P(f(y, z)) ∨ Q(y)`` is ``P(y) ∨ Q(y)``, true for both ``y``. The wrong clause ``P(g(z)) ∨ Q(y)`` is
  ``P(z) ∨ Q(y)``, false at ``y = 0, z = 1``.
* (B) ``P(f(y, x)) ∨ Q(y)``. The matcher is ``{x: y, y: x}`` (cyclic, following it never ends); the instance is
  ``f(y, x) = g(y)``, so the right result is ``P(g(y)) ∨ Q(y)``. The clause ``P(g(x)) ∨ Q(y)`` does not follow
  (the same structure: ``P(x) ∨ Q(y)`` is false at ``x = 1, y = 0``).
* (C) ``P(f(x, y)) ∨ Q(y)``. The matcher is ``{x: x, y: y}`` (each variable bound to itself); the instance is
  ``f(x, y) = g(x)`` and the right result is ``P(g(x)) ∨ Q(y)``.

A UNIFIER is different: two-sided unification binds variables of both clauses and its bindings are triangular
(``{x: y, y: a}`` says ``x`` is ``a``), so the output of a unifier IS followed. ``{P(x, x), Q(x)}`` with
``{¬P(y, a)}`` resolves to ``{Q(a)}``, not to ``{Q(y)}``.
"""
import itertools
import random

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import resolution
from unicode_logic_kit.atp import resolution_check
from unicode_logic_kit.atp.resolution_check import (
    ResolutionDerivation, ResolutionStep, _apply, _match_term, _unify, verify_resolution_proof,
)
from unicode_logic_kit.atp.tstp import parse_tstp_derivation
from unicode_logic_kit.atp.tstp_check import _check_tstp_demodulation, check_tstp_derivation
from unicode_logic_kit.fol.nodes import Atom, Constant, Function, Not, Or, Variable

x, y, z = Variable("x"), Variable("y"), Variable("z")


def f(*args):
    return Function("f", list(args))


def g(*args):
    return Function("g", list(args))


def P(term):
    return Atom("P", [term])


def Q(term):
    return Atom("Q", [term])


RULE_ATOM = Atom("=", [f(x, y), g(x)])               # f(x, y) = g(x)
REVERSED_ATOM = Atom("=", [g(x), f(x, y)])           # the same equation written the other way round

CLAUSE_A = frozenset([P(f(y, z)), Q(y)])
RIGHT_A = frozenset([P(g(y)), Q(y)])
CHAINED_A = frozenset([P(g(z)), Q(y)])
CLAUSE_B = frozenset([P(f(y, x)), Q(y)])
RIGHT_B = frozenset([P(g(y)), Q(y)])
WRONG_B = frozenset([P(g(x)), Q(y)])
CLAUSE_C = frozenset([P(f(x, y)), Q(y)])
RIGHT_C = frozenset([P(g(x)), Q(y)])


# ---------------------------------------------------------------------------------------------
# the hand derivation, checked by enumeration (so that the tests below test the checkers, not a slip)
# ---------------------------------------------------------------------------------------------
def test_the_chained_clauses_do_not_follow_and_the_right_ones_do():
    universe = (0, 1)
    in_p, in_q = {0}, {1}

    def f_of(u, v):                                  # f(u, v) = u
        return u

    def g_of(u):                                     # g(u) = u
        return u

    assert all(f_of(u, v) == g_of(u) for u, v in itertools.product(universe, repeat=2))      # the equation holds
    for yy, zz in itertools.product(universe, repeat=2):
        assert f_of(yy, zz) in in_p or yy in in_q                      # P(f(y, z)) ∨ Q(y): the target holds
        assert g_of(yy) in in_p or yy in in_q                          # P(g(y)) ∨ Q(y): the right result holds
    assert not (g_of(1) in in_p or 0 in in_q)                          # P(g(z)) ∨ Q(y) at y = 0, z = 1: false
    for yy, xx in itertools.product(universe, repeat=2):
        assert f_of(yy, xx) in in_p or yy in in_q                      # P(f(y, x)) ∨ Q(y): the target of (B) holds
    assert not (g_of(1) in in_p or 0 in in_q)                          # P(g(x)) ∨ Q(y) at x = 1, y = 0: false


# ---------------------------------------------------------------------------------------------
# the matcher application
# ---------------------------------------------------------------------------------------------
def test_a_matcher_is_applied_in_one_step_and_a_unifier_is_followed():
    matcher = _match_term(f(x, y), f(y, z), {})
    assert matcher == {"x": y, "y": z}
    assert resolution_check._apply_matcher(g(x), matcher) == g(y)                    # the image y is the clause's y
    assert _apply(g(x), matcher) == g(z)                            # what following the chain would read
    unifier = _unify(Atom("P", [x, x]), Atom("P", [y, Constant("a")]))
    assert _apply(Atom("Q", [x]), unifier) == Atom("Q", [Constant("a")])     # a unifier's bindings are triangular


def test_a_cyclic_matcher_and_a_matcher_binding_a_variable_to_itself_are_applied():
    cyclic = _match_term(f(x, y), f(y, x), {})
    assert cyclic == {"x": y, "y": x}
    assert resolution_check._apply_matcher(g(x), cyclic) == g(y)
    assert resolution_check._apply_matcher(f(y, x), cyclic) == f(x, y)               # a swap, in one step
    identity = _match_term(f(x, y), f(x, y), {})
    assert identity == {"x": x, "y": y}
    assert resolution_check._apply_matcher(g(x), identity) == g(x)


def test_a_variable_the_matcher_does_not_bind_is_left_as_it_is():
    matcher = _match_term(f(x, y), f(Constant("a"), Constant("b")), {})
    assert resolution_check._apply_matcher(g(Variable("w"), x), matcher) == g(Variable("w"), Constant("a"))


# ---------------------------------------------------------------------------------------------
# resolution_check
# ---------------------------------------------------------------------------------------------
def demodulation_step_checks(target, literal, position, stated, equation, direction):
    unit = frozenset([equation])
    steps = (
        ResolutionStep(1, target, "input"),
        ResolutionStep(2, unit, "input"),
        ResolutionStep(3, stated, "demodulate", (1, 2), eq_literal=equation, target_literal=literal,
                       direction=direction, position=position),
    )
    return verify_resolution_proof(ResolutionDerivation((target, unit), steps))


CASES = [("A", CLAUSE_A, P(f(y, z)), RIGHT_A, CHAINED_A), ("B", CLAUSE_B, P(f(y, x)), RIGHT_B, WRONG_B),
         ("C", CLAUSE_C, P(f(x, y)), RIGHT_C, CLAUSE_C)]
EQUATIONS = [(RULE_ATOM, "lr"), (REVERSED_ATOM, "rl")]


@pytest.mark.parametrize("equation,direction", EQUATIONS)
@pytest.mark.parametrize("label,clause,literal,right,wrong", CASES)
def test_resolution_check_accepts_the_right_instance_and_rejects_the_wrong_one(label, clause, literal, right, wrong,
                                                                                equation, direction):
    accepted = demodulation_step_checks(clause, literal, (0,), right, equation, direction)
    assert accepted.ok, (label, accepted.error)
    rejected = demodulation_step_checks(clause, literal, (0,), wrong, equation, direction)
    assert rejected.ok is False and "'demodulate'" in rejected.error, (label, rejected.error)
    assert "recomputed clause is not a variant" in rejected.error


# ---------------------------------------------------------------------------------------------
# tstp_check
# ---------------------------------------------------------------------------------------------
TSTP_CASES = [
    ("A", "(p(f(Y, Z)) | q(Y))", "(p(g(Y)) | q(Y))", "(p(g(Z)) | q(Y))", Or(P(f(y, z)), Q(y))),
    ("B", "(p(f(Y, X)) | q(Y))", "(p(g(Y)) | q(Y))", "(p(g(X)) | q(Y))", Or(P(f(y, x)), Q(y))),
    ("C", "(p(f(X, Y)) | q(Y))", "(p(g(X)) | q(Y))", "(p(f(X, Y)) | q(Y))", Or(P(f(x, y)), Q(y))),
]


def tstp_demodulation(target_text, stated_text, target_formula, equation_text):
    equation = RULE_ATOM if equation_text.startswith("f") else REVERSED_ATOM
    text = (
        f"cnf(c1, axiom, ({equation_text})).\n"
        f"cnf(c2, axiom, {target_text}).\n"
        f"cnf(c3, plain, {stated_text}, inference(forward_demodulation,[],[c2,c1])).\n"
    )
    return check_tstp_derivation(parse_tstp_derivation(text), [equation, target_formula], None, query="refutation")


@pytest.mark.parametrize("equation_text", ["f(X, Y) = g(X)", "g(X) = f(X, Y)"])
@pytest.mark.parametrize("label,target_text,right_text,wrong_text,target_formula", TSTP_CASES)
def test_tstp_check_accepts_the_right_instance_and_rejects_the_wrong_one(label, target_text, right_text, wrong_text,
                                                                          target_formula, equation_text):
    accepted = tstp_demodulation(target_text, right_text, target_formula, equation_text)
    assert accepted.verified, (label, accepted.error)
    rejected = tstp_demodulation(target_text, wrong_text, target_formula, equation_text)
    assert rejected.verified is False and "demodulation" in rejected.error, (label, rejected.error)


def test_the_tstp_demodulation_search_gives_a_verdict_for_every_matcher_shape():
    # the search tries every position and direction, so the cyclic and the self-binding matchers are met in the
    # ordinary course of checking one step: a verdict, never an exception
    for clause, right in ((CLAUSE_A, RIGHT_A), (CLAUSE_B, RIGHT_B), (CLAUSE_C, RIGHT_C)):
        unit = frozenset([RULE_ATOM])
        assert _check_tstp_demodulation(right, clause, unit) is None
        assert _check_tstp_demodulation(right, unit, clause) is None          # the parents in the other order
        assert _check_tstp_demodulation(frozenset([P(g(Variable("w")))]), clause, unit) is not None


# ---------------------------------------------------------------------------------------------
# the output of a unifier keeps being followed
# ---------------------------------------------------------------------------------------------
def test_resolution_check_follows_the_bindings_of_a_unifier():
    # {P(x, x), Q(x)} and {¬P(y, a)}: standardized apart, P(_L0, _L0) against P(_R0, a) gives {_L0: _R0, _R0: a}
    c1 = frozenset([Atom("P", [x, x]), Q(x)])
    c2 = frozenset([Not(Atom("P", [y, Constant("a")]))])

    def check(stated):
        steps = (ResolutionStep(1, c1, "input"), ResolutionStep(2, c2, "input"),
                 ResolutionStep(3, stated, "resolve", (1, 2)))
        return verify_resolution_proof(ResolutionDerivation((c1, c2), steps))

    assert check(frozenset([Q(Constant("a"))])).ok
    assert check(frozenset([Q(y)])).ok is False


def test_tstp_check_follows_the_bindings_of_a_unifier():
    text = (
        "cnf(c1, axiom, (p(X, X) | q(X))).\n"
        "cnf(c2, axiom, ~p(Y, a)).\n"
        "cnf(c3, plain, {stated}, inference(resolution,[],[c1,c2])).\n"
    )
    premises = [Or(Atom("P", [x, x]), Q(x)), Not(Atom("P", [y, Constant("a")]))]
    right = check_tstp_derivation(parse_tstp_derivation(text.format(stated="q(a)")), premises, None, query="refutation")
    wrong = check_tstp_derivation(parse_tstp_derivation(text.format(stated="q(Z)")), premises, None, query="refutation")
    assert right.verified, right.error
    assert wrong.verified is False and "resolution" in wrong.error


# ---------------------------------------------------------------------------------------------
# the prover
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("label,clause,literal,right,wrong", CASES)
def test_the_prover_rewrites_with_the_instance_of_the_rule(label, clause, literal, right, wrong):
    rule = (f(x, y), g(x))
    assert resolution._demodulate_once(clause, [rule]) == right, label


def test_a_chained_matcher_ends_in_the_right_clause_after_the_fixpoint():
    rule = (f(x, y), g(x))
    clause, count = resolution._demodulate_to_fixpoint(CLAUSE_A, [rule])
    assert clause == RIGHT_A and count == 1


@pytest.mark.parametrize("backend", ["resolution", "z3"])
def test_no_wrong_proof_through_a_chained_matcher(backend):
    # ∀x ∀y f(x,y) = g(x);  ∀y ∀z ∀w (P(f(y,z)) ∨ P(f(y,w)) ∨ Q(y));  ¬Q(aa).
    # P(g(aa)) follows (y := aa, z := w). P(g(bb)) does NOT: the universe {a, b}, g = identity, f(u, v) = g(u),
    # Q = {b}, P = {a}, aa = a, bb = b makes every premise true and P(g(bb)) = P(b) false.
    premises = [api.parse_any(text).formula for text in (
        "∀x ∀y f(x, y) = g(x)", "∀y ∀z ∀w (P(f(y, z)) ∨ P(f(y, w)) ∨ Q(y))", "¬Q(aa)")]
    follows = api.prove(api.parse_any("P(g(aa))").formula, premises, backends=[backend], timeout=20000)
    assert follows.status == "proved"
    not_follows = api.prove(api.parse_any("P(g(bb))").formula, premises, backends=[backend], timeout=20000)
    assert not_follows.status != "proved"


# ---------------------------------------------------------------------------------------------
# every rewrite the prover makes on generated equational problems is licensed by both checkers
# ---------------------------------------------------------------------------------------------
VARS = [Variable(name) for name in "xyzu"]
CONSTANTS = [Constant(name) for name in ("a", "b", "c")]


def generated_term(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice(VARS) if rng.random() < 0.6 else rng.choice(CONSTANTS)
    name, arity = rng.choice([("f", 1), ("g", 1), ("h", 2)])
    return Function(name, [generated_term(rng, depth - 1) for _ in range(arity)])


def generated_literal(rng):
    if rng.random() < 0.35:
        atom = Atom("=", [generated_term(rng, 2), generated_term(rng, 2)])
    else:
        atom = Atom(rng.choice(["P", "Q"]), [generated_term(rng, 2)])
    return atom if rng.random() < 0.6 else Not(atom)


def generated_problem(rng):
    clauses = [frozenset([Atom("=", [generated_term(rng, 2), generated_term(rng, 2)])])
               for _ in range(rng.randint(1, 3))]
    clauses += [frozenset(generated_literal(rng) for _ in range(rng.randint(1, 3))) for _ in range(rng.randint(2, 4))]
    return clauses


def matcher_chains(sigma):
    return any(isinstance(node, Variable) and node.name in sigma for term in sigma.values() for node in term.walk())


def licensed_by_resolution_check(target, rules, new):
    """Some rule, literal and position makes the stated rewrite a step ``verify_resolution_proof`` accepts."""
    for left, right in rules:
        equation = Atom("=", [left, right])
        unit = frozenset([equation])
        for literal in target:
            for position in resolution._subterm_positions(resolution._atom_of(literal)):
                steps = (ResolutionStep(1, target, "input"), ResolutionStep(2, unit, "input"),
                         ResolutionStep(3, new, "demodulate", (1, 2), eq_literal=equation, target_literal=literal,
                                        direction="lr", position=position))
                if verify_resolution_proof(ResolutionDerivation((target, unit), steps)).ok:
                    return True
    return False


def licensed_by_tstp_check(target, rules, new):
    return any(_check_tstp_demodulation(new, target, frozenset([Atom("=", [left, right])])) is None
               for left, right in rules)


def test_every_rewrite_of_the_prover_on_generated_problems_is_licensed_by_both_checkers(monkeypatch):
    performed = []
    real = resolution._demodulate_once

    def recording(clause, rules):
        rewritten = real(clause, rules)
        if rewritten is not None:
            performed.append((clause, list(rules), rewritten))
        return rewritten

    monkeypatch.setattr(resolution, "_demodulate_once", recording)
    rng = random.Random(20261005)
    for _ in range(60):
        resolution.refute(generated_problem(rng), max_steps=120, timeout=20000)
    assert len(performed) >= 600, len(performed)                        # the problems do rewrite
    chained = 0
    for index, (clause, rules, rewritten) in enumerate(performed):
        # a clause is counted as chained when some rule of the call matches some subterm of it with a chained matcher
        is_chained = any(
            matcher_chains(sigma)
            for lit in clause for pos in resolution._subterm_positions(resolution._atom_of(lit))
            for left, _right in rules
            for sigma in [resolution._match_term(left, resolution._term_at(resolution._atom_of(lit), pos), {})]
            if sigma is not None)
        chained += is_chained
        assert licensed_by_resolution_check(clause, rules, rewritten), (index, clause, rules, rewritten)
        assert licensed_by_tstp_check(clause, rules, rewritten), (index, clause, rules, rewritten)
    assert chained >= 20, chained                                        # and chained matchers are among them
