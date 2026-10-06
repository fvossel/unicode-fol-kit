"""Twee names the clauses of a conjunctive premise in an order of its own.

A premise ``i`` that is a conjunction of ``n`` equations is clausified by Twee into one
clause per conjunct, named ``premise_<i>``, ``premise_<i>_1``, ... ``premise_<i>_<n - 1>``.
Which clause carries which suffix is not the order of the source: Twee numbers them in an
order of its own and drops a ground conjunct that repeats an earlier one. A checker that
read ``premise_<i>`` as the FIRST conjunct and ``premise_<i>_<k>`` as the ``k``-th would
compare the equation a proof restates with the wrong conjunct and refuse the genuine
proof of a valid problem. So a name determines the premise and nothing more: the
restated equation has to be one of the conjuncts of THAT premise, up to the renaming of
its variables, whichever suffix Twee gave it.

Every proof text below is a verbatim ``twee --quiet`` stdout (Twee 2.6.1, WSL) for the
problem named above it.
"""

import dataclasses

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.twee_backend import TweeBackend
from unicode_fol_kit.atp.twee_check import (
    _expected_axiom_equations, check_twee_proof, goal_matches_conclusion,
)
from unicode_fol_kit.atp.twee_entailment import parse_twee_proof, twee_available
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Function, Quantifier, Variable

_X, _Y = Variable("x"), Variable("y")
_AA, _BB, _CC, _DD = (Constant(name) for name in ("aa", "bb", "cc", "dd"))


def _app(name, *args):
    return Function(name, list(args))


def _eq(left, right):
    return Atom("=", [left, right])


def _all(variable, body):
    return Quantifier("∀", variable, body)


def _and(*parts):
    result = parts[0]
    for part in parts[1:]:
        result = And(result, part)
    return result


_AA_BB = _eq(_AA, _BB)
_CC_DD = _eq(_CC, _DD)
_FX_X = _all(_X, _eq(_app("ff", _X), _X))                                # ∀x ff(x) = x
_GX_X = _all(_X, _eq(_app("gg", _X), _X))                                # ∀x gg(x) = x
_COMMUTATIVE = _all(_X, _all(_Y, _eq(_app("hh", _X, _Y), _app("hh", _Y, _X))))   # ∀x ∀y hh(x, y) = hh(y, x)
_ALL_EQUAL = _all(_X, _all(_Y, _eq(_X, _Y)))                             # ∀x ∀y x = y

# Premise ``aa = bb ∧ ∀x ff(x) = x``: the SECOND conjunct is ``premise_1``.
_PROOF_SECOND_CONJUNCT_FIRST = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): ff(X) = X.

Goal 1 (goal): ff(ff(cc)) = cc.
Proof:
  ff(ff(cc))
= { by axiom 1 (premise_1) }
  ff(cc)
= { by axiom 1 (premise_1) }
  cc

RESULT: Theorem (the conjecture is true).
"""

# Premise ``aa = bb ∧ ∀x ∀y x = y``.
_PROOF_ALL_EQUAL = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): X = Y.

Goal 1 (goal): cc = dd.
Proof:
  cc
= { by axiom 1 (premise_1) R->L }
  dd

RESULT: Theorem (the conjecture is true).
"""

# Premise ``aa = bb ∧ aa = bb ∧ cc = dd``: the repeated ground conjunct is dropped, and
# ``cc = dd`` (the THIRD conjunct of the source) is ``premise_1_1``.
_PROOF_REPEAT_DROPPED = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1_1): cc = dd.

Goal 1 (goal): cc = dd.
Proof:
  cc
= { by axiom 1 (premise_1_1) }
  dd

RESULT: Theorem (the conjecture is true).
"""

# Premise ``∀x ∀y hh(x, y) = hh(y, x) ∧ ∀x ff(x) = x``: the two clauses come out swapped.
_PROOF_CLAUSES_SWAPPED = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): ff(X) = X.
Axiom 2 (premise_1_1): hh(X, Y) = hh(Y, X).

Goal 1 (goal): hh(ff(aa), bb) = hh(bb, aa).
Proof:
  hh(ff(aa), bb)
= { by axiom 2 (premise_1_1) R->L }
  hh(bb, ff(aa))
= { by axiom 1 (premise_1) }
  hh(bb, aa)

RESULT: Theorem (the conjecture is true).
"""

# Premises ``aa = bb`` and ``cc = dd ∧ ∀x ff(x) = x``: the clause with a variable is
# ``premise_2`` and the ground conjunct, the first of the source, is ``premise_2_1``.
_PROOF_SECOND_PREMISE = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_2_1): cc = dd.
Axiom 2 (premise_2): ff(X) = X.

Goal 1 (goal): ff(ff(cc)) = dd.
Proof:
  ff(ff(cc))
= { by axiom 1 (premise_2_1) }
  ff(ff(dd))
= { by axiom 2 (premise_2) }
  ff(dd)
= { by axiom 2 (premise_2) }
  dd

RESULT: Theorem (the conjecture is true).
"""

# Premise ``∀x gg(x) = x ∧ ∀x ff(x) = x ∧ cc = dd ∧ aa = bb``: here the clauses ARE in the
# order of the source.
_PROOF_SOURCE_ORDER = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1_2): cc = dd.
Axiom 2 (premise_1_1): ff(X) = X.
Axiom 3 (premise_1): gg(X) = X.

Goal 1 (goal): gg(ff(cc)) = cc.
Proof:
  gg(ff(cc))
= { by axiom 1 (premise_1_2) }
  gg(ff(dd))
= { by axiom 2 (premise_1_1) }
  gg(dd)
= { by axiom 3 (premise_1) }
  dd
= { by axiom 1 (premise_1_2) R->L }
  cc

RESULT: Theorem (the conjecture is true).
"""

_CASES = {
    "second conjunct first": (_PROOF_SECOND_CONJUNCT_FIRST, [_and(_AA_BB, _FX_X)],
                              _eq(_app("ff", _app("ff", _CC)), _CC)),
    "all elements equal": (_PROOF_ALL_EQUAL, [_and(_AA_BB, _ALL_EQUAL)], _CC_DD),
    "repeat dropped": (_PROOF_REPEAT_DROPPED, [_and(_AA_BB, _AA_BB, _CC_DD)], _CC_DD),
    "clauses swapped": (_PROOF_CLAUSES_SWAPPED, [_and(_COMMUTATIVE, _FX_X)],
                        _eq(_app("hh", _app("ff", _AA), _BB), _app("hh", _BB, _AA))),
    "second premise": (_PROOF_SECOND_PREMISE, [_AA_BB, _and(_CC_DD, _FX_X)],
                       _eq(_app("ff", _app("ff", _CC)), _DD)),
    "source order": (_PROOF_SOURCE_ORDER, [_and(_GX_X, _FX_X, _CC_DD, _AA_BB)],
                     _eq(_app("gg", _app("ff", _CC)), _CC)),
}


# ---------------------------------------------------------------------------
# A genuine proof is accepted whichever clause carries which name
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("label", sorted(_CASES))
def test_a_genuine_proof_of_a_conjunctive_premise_is_checked_by_what_each_axiom_says(label):
    """Each problem is valid by a derivation from one conjunct (``ff(ff(cc)) = cc`` from
    ``ff(X) = X`` twice; ``cc = dd`` from ``X = Y`` or from the conjunct itself;
    ``hh(ff(aa), bb) = hh(bb, aa)`` by commutativity and ``ff(aa) = aa``; ...), and the proof
    Twee printed for it is checked against the premises as the caller wrote them."""
    text, premises, conclusion = _CASES[label]
    proof = parse_twee_proof(text)
    result = check_twee_proof(proof, premises)
    assert result.ok, result.error
    assert goal_matches_conclusion(proof, conclusion) is True


@pytest.mark.parametrize("label", sorted(_CASES))
def test_the_backend_proves_what_the_checker_accepts(label, monkeypatch):
    """The two checks of the backend, with the runner returning the proof text above."""
    text, premises, conclusion = _CASES[label]
    monkeypatch.setattr("unicode_fol_kit.atp.twee_entailment._spawn_twee",
                        lambda *args, **kwargs: (text, "", False))
    verdict = TweeBackend().decide(conclusion, premises)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)


def test_the_expected_names_of_a_premise_all_carry_its_whole_list_of_conjuncts():
    """A premise of three conjuncts has the names ``premise_1``, ``premise_1_1``, ``premise_1_2``;
    each stands for any of the three equations, and the other premise has its own names."""
    mapping = _expected_axiom_equations([_and(_AA_BB, _CC_DD, _FX_X), _AA_BB])
    assert set(mapping) == {"premise_1", "premise_1_1", "premise_1_2", "premise_2"}
    assert len(mapping["premise_1"]) == len(mapping["premise_1_1"]) == len(mapping["premise_1_2"]) == 3
    assert mapping["premise_1"] == mapping["premise_1_2"]
    assert len(mapping["premise_2"]) == 1


# ---------------------------------------------------------------------------
# What is refused: the name determines the premise
# ---------------------------------------------------------------------------

def test_an_axiom_that_says_something_no_conjunct_says_is_refused_whatever_it_is_called():
    """The proof of ``ff(ff(cc)) = cc`` with its axiom restated as ``gg(X) = X``: neither
    conjunct of ``aa = bb ∧ ∀x ff(x) = x`` says that."""
    proof = parse_twee_proof(_PROOF_SECOND_CONJUNCT_FIRST)
    forged = dataclasses.replace(
        proof.axioms[0], equation=dataclasses.replace(
            proof.axioms[0].equation, lhs=_app("gg", Variable("X"))))
    result = check_twee_proof(dataclasses.replace(proof, axioms=(forged,)), [_and(_AA_BB, _FX_X)])
    assert not result.ok
    assert "not alpha-equivalent" in result.error


def test_an_axiom_named_for_one_premise_may_not_be_a_conjunct_of_another():
    """The clause ``cc = dd`` is a conjunct of premise 2 only; a proof that calls it
    ``premise_1`` (premise 1 is ``aa = bb``) cites a premise that does not say it."""
    proof = parse_twee_proof(_PROOF_SECOND_PREMISE.replace("premise_2_1", "premise_1"))
    result = check_twee_proof(proof, [_AA_BB, _and(_CC_DD, _FX_X)])
    assert not result.ok
    assert "not alpha-equivalent" in result.error
    assert check_twee_proof(parse_twee_proof(_PROOF_SECOND_PREMISE),
                            [_AA_BB, _and(_CC_DD, _FX_X)]).ok


def test_a_suffix_beyond_the_last_conjunct_is_not_a_clause_of_the_premise():
    """``∀x ∀y hh(x, y) = hh(y, x) ∧ ∀x ff(x) = x`` has two conjuncts, so the names
    ``premise_1`` and ``premise_1_1``; ``premise_1_2`` is none of Twee's."""
    proof = parse_twee_proof(_PROOF_CLAUSES_SWAPPED.replace("premise_1_1", "premise_1_2"))
    result = check_twee_proof(proof, [_and(_COMMUTATIVE, _FX_X)])
    assert not result.ok
    assert "premise_1_2" in result.error


def test_the_conjunct_is_not_found_in_a_premise_that_does_not_have_one_like_it():
    """Premise ``aa = bb ∧ ∀x gg(x) = x`` has no conjunct ``ff(X) = X``."""
    proof = parse_twee_proof(_PROOF_SECOND_CONJUNCT_FIRST)
    assert not check_twee_proof(proof, [_and(_AA_BB, _GX_X)]).ok


# ---------------------------------------------------------------------------
# Real Twee, through WSL, and the problems of the proofs above
# ---------------------------------------------------------------------------

needs_twee = pytest.mark.skipif(not twee_available(), reason="no Twee binary reachable via WSL")


@needs_twee
@pytest.mark.parametrize("label", ["second conjunct first", "all elements equal", "repeat dropped",
                                   "clauses swapped", "second premise"])
def test_live_twee_proves_the_problem_and_the_kit_verifies_the_proof(label):
    _text, premises, conclusion = _CASES[label]
    verdict = api.prove(conclusion, premises, backends=["twee"], timeout=30000)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)
    assert "independently verified" in verdict.detail


@needs_twee
def test_live_a_conjunctive_premise_does_not_prove_what_does_not_follow():
    """``aa = bb ∧ ∀x ff(x) = x`` says nothing about ``gg``: universe ``{0, 1}``, ``ff`` the
    identity, ``gg(0) = 1``, ``cc`` ↦ 0, so ``gg(cc) = cc`` fails."""
    verdict = api.prove(_eq(_app("gg", _CC), _CC), [_and(_AA_BB, _FX_X)], backends=["twee"],
                        timeout=30000)
    assert verdict.status == "refuted", (verdict.reason, verdict.detail)
