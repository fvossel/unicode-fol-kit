"""Twee and conclusions that repeat a conjunct, and Twee problems with sorted constants.

**Duplicate conjuncts.** Twee's clausifier drops a repeated GROUND conjunct, so for
``f(a) = b ∧ f(a) = b`` it proves the single goal ``f(a) = b`` (and for
``f(a) = b ∧ g(a) = c ∧ f(a) = b`` the pair ``tuple(f(a), g(a)) = tuple(b, c)``), while
two conjuncts with variables apart each keep their own Skolem terms. The kit's goal
check used to compare the goal with the conjuncts of the conclusion as written, so a
true theorem with a repeated ground conjunct was reported ``error`` / ``infra`` instead of
``proved``. ``A ∧ A`` is ``A``: the repeats are one conjunct. What did NOT change, and
is pinned below by tampered variants: the goal still has to restate the (distinct)
conjuncts exactly, a proof of ``A`` is not a proof of ``A ∧ B``, and a conjunct is still
matched under an injective substitution, so a proof of a ground equation never certifies
the universally quantified claim, with or without copies.

**Sorted constants.** The problem the kit hands to Twee carries the sort of ``c:S`` as
a ``sort_member`` axiom and writes the constant itself plainly, so Twee's proof speaks of
the plain constant ``c``. The proof checker compared that with the premise as the caller
wrote it (``f(c:S) = b``) and rejected it, so every sorted constant in an equational
problem ended as ``error`` / ``infra``. The equations are compared with the sorts read
off (the sort is a premise of the problem, never part of an equation), and Twee answers
such a problem as Z3 does.

Every proof text below is a verbatim ``twee --quiet`` stdout captured on this machine
(Twee 2.6.1, WSL) for the problem named above it.
"""

import dataclasses

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.twee_backend import TweeBackend
from unicode_fol_kit.atp.twee_check import check_twee_proof, goal_matches_conclusion
from unicode_fol_kit.atp.twee_entailment import (
    TweeAxiom, TweeChain, TweeCitation, TweeEquation, TweeGoal, TweeProof,
    parse_twee_proof, twee_available,
)
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Quantifier, SortedConstant, Variable,
)

_A, _B, _C, _D = Constant("a"), Constant("b"), Constant("c"), Constant("d")
_X, _Y = Variable("x"), Variable("y")


def _f(term):
    return Function("f", [term])


def _g(term):
    return Function("g", [term])


def _eq(left, right):
    return Atom("=", [left, right])


def _all(variable, body):
    return Quantifier("∀", variable, body)


def _and(*parts):
    result = parts[0]
    for part in parts[1:]:
        result = And(result, part)
    return result


_FA_B = _eq(_f(_A), _B)        # f(a) = b
_GA_C = _eq(_g(_A), _C)        # g(a) = c

# Premises f(a) = b; conclusion f(a) = b ∧ f(a) = b: the goal is the single equation.
_PROOF_REPEATED_GROUND = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): f(a) = b.

Goal 1 (goal): f(a) = b.
Proof:
  f(a)
= { by axiom 1 (premise_1) }
  b

RESULT: Theorem (the conjecture is true).
"""

# Premises f(a) = b, g(a) = c; conclusion (f(a) = b ∧ g(a) = c) ∧ f(a) = b: the goal is the
# pair of the two DISTINCT conjuncts.
_PROOF_PAIR_WITH_REPEAT = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_2): g(a) = c.
Axiom 2 (premise_1): f(a) = b.

Goal 1 (goal): tuple(f(a), g(a)) = tuple(b, c).
Proof:
  tuple(f(a), g(a))
= { by axiom 2 (premise_1) }
  tuple(b, g(a))
= { by axiom 1 (premise_2) }
  tuple(b, c)

RESULT: Theorem (the conjecture is true).
"""

# Premise ∀x f(x) = x; conclusion ∀x (f(x) = x ∧ f(x) = x): with a variable the two conjuncts
# are NOT merged, each keeps its own Skolem term.
_PROOF_REPEATED_UNDER_QUANTIFIER = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): f(X) = X.

Goal 1 (goal): tuple(f(x2), f(x)) = tuple(x2, x).
Proof:
  tuple(f(x2), f(x))
= { by axiom 1 (premise_1) }
  tuple(f(x2), x)
= { by axiom 1 (premise_1) }
  tuple(x2, x)

RESULT: Theorem (the conjecture is true).
"""

# Premise ∀x f(f(x)) = x; conclusion f(f(f(f(anna:Person)))) = anna:Person (the problem the
# kit hands over has the sort_member axiom person(anna) and the plain constant anna).
_PROOF_SORTED_CONCLUSION = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): f(f(X)) = X.

Goal 1 (goal): f(f(f(f(anna)))) = anna.
Proof:
  f(f(f(f(anna))))
= { by axiom 1 (premise_1) }
  f(f(anna))
= { by axiom 1 (premise_1) }
  anna

RESULT: Theorem (the conjecture is true).
"""

# Premise f(anna:Person) = b; conclusion f(anna) = b.
_PROOF_SORTED_PREMISE = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): f(anna) = b.

Goal 1 (goal): f(anna) = b.
Proof:
  f(anna)
= { by axiom 1 (premise_1) }
  b

RESULT: Theorem (the conjecture is true).
"""


# ---------------------------------------------------------------------------
# A conjunct that repeats another is one conjunct
# ---------------------------------------------------------------------------

def test_a_ground_conjunct_written_twice_is_matched_by_the_proof_of_the_single_equation():
    """Twee proves ``f(a) = b`` for ``f(a) = b ∧ f(a) = b``, and ``A ∧ A`` is ``A``."""
    proof = parse_twee_proof(_PROOF_REPEATED_GROUND)
    assert check_twee_proof(proof, [_FA_B]).ok
    assert goal_matches_conclusion(proof, _and(_FA_B, _FA_B)) is True
    assert goal_matches_conclusion(proof, _and(_FA_B, _and(_FA_B, _FA_B))) is True


@pytest.mark.parametrize("conclusion", [
    _and(_FA_B, _GA_C, _FA_B),      # A ∧ B ∧ A
    _and(_FA_B, _FA_B, _GA_C),      # A ∧ A ∧ B
    _and(_GA_C, _FA_B, _FA_B),      # B ∧ A ∧ A
    _and(_FA_B, _GA_C),             # A ∧ B, no repeat: matched as before
], ids=["ABA", "AAB", "BAA", "AB"])
def test_the_pair_of_distinct_conjuncts_matches_whichever_order_and_repeats_the_conclusion_has(
        conclusion):
    """The goal ``tuple(f(a), g(a)) = tuple(b, c)`` restates the distinct conjuncts ``A``, ``B``."""
    proof = parse_twee_proof(_PROOF_PAIR_WITH_REPEAT)
    assert check_twee_proof(proof, [_FA_B, _GA_C]).ok
    assert goal_matches_conclusion(proof, conclusion) is True


def test_variables_keep_two_conjuncts_apart_and_the_goal_matches_as_it_always_did():
    """With a variable Twee keeps ``f(x) = x`` twice (``tuple(f(x2), f(x)) = tuple(x2, x)``),
    which is the conjuncts as written."""
    proof = parse_twee_proof(_PROOF_REPEATED_UNDER_QUANTIFIER)
    premise = _all(_X, _eq(_f(_X), _X))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, _all(_X, _and(_eq(_f(_X), _X), _eq(_f(_X), _X)))) is True


# ---------------------------------------------------------------------------
# What the repeat rule does not loosen (tampered variants)
# ---------------------------------------------------------------------------

def test_a_proof_of_one_equation_is_not_a_proof_of_it_together_with_another():
    proof = parse_twee_proof(_PROOF_REPEATED_GROUND)
    assert goal_matches_conclusion(proof, _and(_FA_B, _GA_C)) is False
    assert goal_matches_conclusion(proof, _and(_FA_B, _FA_B, _GA_C)) is False
    assert goal_matches_conclusion(proof, _and(_GA_C, _GA_C)) is False


def test_a_proof_of_one_repeated_equation_is_not_a_proof_of_another_repeated_equation():
    """``f(a) = b`` is the goal; ``g(a) = c ∧ g(a) = c`` is one conjunct, but a different one."""
    proof = parse_twee_proof(_PROOF_REPEATED_GROUND)
    assert goal_matches_conclusion(proof, _and(_GA_C, _GA_C)) is False
    assert goal_matches_conclusion(proof, _and(_eq(_f(_A), _C), _eq(_f(_A), _C))) is False


def test_a_tampered_pair_goal_does_not_match_a_conclusion_with_a_repeat():
    """The pair proves ``g(a) = c``; a conclusion that asks ``g(a) = d`` (twice over) is not it."""
    proof = parse_twee_proof(_PROOF_PAIR_WITH_REPEAT)
    other_second = _eq(_g(_A), _D)
    assert goal_matches_conclusion(proof, _and(_FA_B, other_second, _FA_B)) is False
    tampered_goal = dataclasses.replace(
        proof.goal, equation=TweeEquation(proof.goal.equation.lhs, Function("tuple", [_B, _D])))
    tampered = dataclasses.replace(proof, goal=tampered_goal)
    assert goal_matches_conclusion(tampered, _and(_FA_B, _GA_C, _FA_B)) is False
    assert goal_matches_conclusion(tampered, _and(_FA_B, _GA_C)) is False


def test_a_pair_goal_that_repeats_one_equation_is_not_a_proof_of_two_distinct_ones():
    """``tuple(f(a), f(a)) = tuple(b, b)`` is a goal about ``f(a) = b`` only."""
    proof = parse_twee_proof(_PROOF_PAIR_WITH_REPEAT)
    pair = Function("tuple", [_f(_A), _f(_A)])
    other = Function("tuple", [_B, _B])
    tampered = dataclasses.replace(
        proof, goal=dataclasses.replace(proof.goal, equation=TweeEquation(pair, other)))
    assert goal_matches_conclusion(tampered, _and(_FA_B, _GA_C, _FA_B)) is False
    assert goal_matches_conclusion(tampered, _and(_FA_B, _GA_C)) is False


def _proof_of_ground_equation_between_f_and_g():
    """The proof of the GROUND fact ``f(a) = g(a)`` from the premise ``f(a) = g(a)``; its
    chain is valid (the checker accepts it)."""
    a = Constant("alpha")
    f_a, g_a = _f(a), _g(a)
    proof = TweeProof(
        axioms=(TweeAxiom(1, "premise_1", TweeEquation(f_a, g_a)),),
        lemmas=(),
        goal=TweeGoal(1, "goal", TweeEquation(f_a, g_a),
                      TweeChain(terms=(f_a, g_a),
                                citations=(TweeCitation("axiom", 1, "premise_1"),))))
    return proof, _eq(f_a, g_a)


def test_a_ground_proof_never_certifies_a_universal_claim_with_or_without_copies():
    """``f(alpha) = g(alpha)`` gives neither ``∀x f(x) = g(x)`` nor ``∀x ∀y f(x) = g(y)``.
    The first is not valid (universe ``{0, 1}``, ``alpha`` ↦ 0, ``f`` ↦ (0, 0), ``g`` ↦
    (0, 1)): the goal is its instance at ``alpha``, a constant of the premise, and only a
    constant of its own (one that occurs in no axiom) can stand for a universally quantified
    variable. The second would also be matched by sending both variables to the one term
    ``alpha``, which Skolemising two universals can not do. Writing the claim twice (or with
    the variables renamed, which is the same claim) must not turn the refusal into a match."""
    proof, premise = _proof_of_ground_equation_between_f_and_g()
    assert check_twee_proof(proof, [premise]).ok
    one = _all(_X, _eq(_f(_X), _g(_X)))
    claim = _all(_X, _all(_Y, _eq(_f(_X), _g(_Y))))
    renamed = _all(Variable("u"), _all(Variable("v"), _eq(_f(Variable("u")), _g(Variable("v")))))
    assert goal_matches_conclusion(proof, one) is False
    assert goal_matches_conclusion(proof, _and(one, one)) is False
    assert goal_matches_conclusion(proof, _and(one, claim)) is False
    assert goal_matches_conclusion(proof, claim) is False
    assert goal_matches_conclusion(proof, _and(claim, claim)) is False
    assert goal_matches_conclusion(proof, _and(claim, renamed)) is False
    assert goal_matches_conclusion(proof, premise) is True


def test_a_ground_proof_certifies_its_own_equation_written_twice():
    proof, premise = _proof_of_ground_equation_between_f_and_g()
    assert goal_matches_conclusion(proof, _and(premise, premise)) is True


def test_the_same_equation_read_in_the_other_direction_is_not_a_repeat():
    """``f(a) = b ∧ b = f(a)`` has two conjuncts; the goal ``f(a) = b`` restates only one."""
    proof = parse_twee_proof(_PROOF_REPEATED_GROUND)
    assert goal_matches_conclusion(proof, _and(_FA_B, _eq(_B, _f(_A)))) is False


# ---------------------------------------------------------------------------
# Sorted constants in an equational problem
# ---------------------------------------------------------------------------

_ANNA = SortedConstant("anna", "Person")


def test_a_proof_about_a_sorted_constant_is_checked_against_the_plain_constant():
    """The goal of the problem with ``anna:Person`` is printed with the plain ``anna``, and the
    chain is valid; the premise and the conclusion are as the caller wrote them."""
    proof = parse_twee_proof(_PROOF_SORTED_CONCLUSION)
    premise = _all(_X, _eq(_f(_f(_X)), _X))
    conclusion = _eq(_f(_f(_f(_f(_ANNA)))), _ANNA)
    result = check_twee_proof(proof, [premise])
    assert result.ok, result.error
    assert goal_matches_conclusion(proof, conclusion) is True


def test_a_sorted_constant_in_a_premise_is_matched_with_the_axiom_twee_cites():
    proof = parse_twee_proof(_PROOF_SORTED_PREMISE)
    premise = _eq(_f(_ANNA), _B)
    result = check_twee_proof(proof, [premise])
    assert result.ok, result.error
    assert goal_matches_conclusion(proof, _eq(_f(Constant("anna")), _B)) is True
    assert goal_matches_conclusion(proof, _eq(_f(_ANNA), _B)) is True


def test_reading_the_sorts_off_still_compares_names_and_structure():
    """Only the sort is dropped: another constant, another right-hand side or another function
    is a different equation, and the checker says so."""
    proof = parse_twee_proof(_PROOF_SORTED_PREMISE)
    for other_premise in (_eq(_f(SortedConstant("carl", "Person")), _B),
                          _eq(_f(_ANNA), _C),
                          _eq(_g(_ANNA), _B)):
        assert not check_twee_proof(proof, [other_premise]).ok, other_premise.to_unicode_str()
    for other_conclusion in (_eq(_f(SortedConstant("carl", "Person")), _B),
                             _eq(_f(_ANNA), _C)):
        assert goal_matches_conclusion(proof, other_conclusion) is False


def test_a_tampered_proof_about_a_sorted_constant_is_still_rejected():
    """The chain of the goal is cut short so that it ends on ``c`` instead of ``b``: no cited
    equation takes ``f(anna)`` to ``c``."""
    proof = parse_twee_proof(_PROOF_SORTED_PREMISE)
    chain = proof.goal.chain
    bad_chain = dataclasses.replace(chain, terms=(chain.terms[0], _C))
    bad = dataclasses.replace(proof, goal=dataclasses.replace(proof.goal, chain=bad_chain))
    assert not check_twee_proof(bad, [_eq(_f(_ANNA), _B)]).ok


# ---------------------------------------------------------------------------
# Live: the real Twee, and Z3 as the other oracle
# ---------------------------------------------------------------------------

_TWEE_AVAILABLE = twee_available()
_live = pytest.mark.skipif(not _TWEE_AVAILABLE, reason="no Twee binary reachable via WSL")


def _answer(backend, conclusion, premises):
    verdict = api.prove(conclusion, premises, backends=[backend], timeout=30000)
    return verdict.status


_REPEATED = {
    "ground twice": ([_FA_B], _and(_FA_B, _FA_B)),
    "pair with a repeat": ([_FA_B, _GA_C], _and(_FA_B, _GA_C, _FA_B)),
    "repeat first": ([_FA_B, _GA_C], _and(_FA_B, _FA_B, _GA_C)),
    "under a quantifier": ([_all(_X, _eq(_f(_X), _X))],
                           _all(_X, _and(_eq(_f(_X), _X), _eq(_f(_X), _X)))),
    "two quantified copies": ([_all(_X, _eq(_f(_X), _X))],
                              _and(_all(_X, _eq(_f(_X), _X)), _all(_Y, _eq(_f(_Y), _Y)))),
}


@_live
@pytest.mark.parametrize("label", sorted(_REPEATED))
def test_live_a_true_theorem_with_a_repeated_conjunct_is_proved_and_checked(label):
    premises, conclusion = _REPEATED[label]
    verdict = TweeBackend().decide(conclusion, premises, timeout=30000)
    assert verdict.status == "proved", (verdict.status, verdict.reason, verdict.detail)
    assert "independently verified" in verdict.detail


@_live
def test_live_a_repeated_conjunct_that_does_not_follow_is_still_refuted_not_proved():
    for premises, conclusion in (
            ([_FA_B], _and(_GA_C, _GA_C)),
            ([_FA_B], _and(_and(_FA_B, _GA_C), _FA_B))):
        verdict = TweeBackend().decide(conclusion, premises, timeout=30000)
        assert verdict.status == "refuted", (verdict.status, verdict.reason, verdict.detail)


_SORTED = {
    "sorted premise, plain conclusion": ([_eq(_f(SortedConstant("a", "S")), _B)],
                                         _eq(_f(_A), _B)),
    "sorted premise, other conclusion": ([_eq(_f(SortedConstant("a", "S")), _B)], _eq(_f(_A), _C)),
    "plain premise, sorted conclusion": ([_FA_B], _eq(_f(SortedConstant("a", "S")), _B)),
    "sorted on both sides": ([_eq(_f(SortedConstant("a", "S")), _B)],
                             _eq(_f(SortedConstant("a", "S")), _B)),
    "a chain through the sorted constant": (
        [_eq(_f(SortedConstant("a", "S")), _B), _eq(_g(_B), _C)], _eq(_g(_f(_A)), _C)),
    "a quantified premise, sorted goal": (
        [_all(_X, _eq(_f(_f(_X)), _X))],
        _eq(_f(_f(_f(_f(SortedConstant("a", "S"))))), SortedConstant("a", "S"))),
    "two conjuncts, sorts on different ones": (
        [_eq(_f(SortedConstant("a", "S")), _B), _GA_C],
        _and(_FA_B, _eq(_g(SortedConstant("a", "S")), _C))),
    "a repeat, one copy sorted": (
        [_eq(_f(SortedConstant("a", "S")), _B)], _and(_FA_B, _eq(_f(SortedConstant("a", "S")), _B))),
}


@_live
@pytest.mark.parametrize("label", sorted(_SORTED))
def test_live_twee_answers_a_problem_with_sorted_constants_as_z3_does(label):
    """Hand check of the answers: every problem but ``other conclusion`` holds (the sort of ``a``
    never changes which equations hold of ``a``), and ``f(a) = c`` does not follow from
    ``f(a) = b``. Both provers agree with that, and with each other."""
    premises, conclusion = _SORTED[label]
    expected = "refuted" if label == "sorted premise, other conclusion" else "proved"
    assert _answer("z3", conclusion, premises) == expected
    assert _answer("twee", conclusion, premises) == expected
