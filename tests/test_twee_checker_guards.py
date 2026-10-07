"""Each condition the Twee proof checker's soundness rests on, pinned by a proof that breaks only it.

``check_twee_proof`` and ``goal_mismatch`` accept a proof of ``premises ⊢ conclusion`` only
if every one of the following holds, and each test below hands them a proof in which exactly
one of them fails while everything else is right:

* an axiom the proof restates is a conjunct of a premise it names, which is a universally
  quantified equation or a conjunction of such (no existential premise, no other formula);
* a lemma and the goal are proved by a chain that starts at the left-hand side it states and
  ends at the right-hand side it states (a lemma is used as the equation it STATES);
* a lemma cites only a lemma with a smaller number, an axiom the proof states, under the name
  it was stated with;
* the Skolem constant a goal stands on is a name no axiom, no conclusion and no encoding
  symbol uses, on either side of every equation.

The proofs are written down by hand as the data classes of ``atp.twee_entailment``, in the
shape Twee prints, over three equations whose derivations are one line each:

* ``∀x ff(x) = gg(x)`` and ``∀x gg(x) = hh(x)`` give the lemma ``ff(X) = hh(X)``, and the goal
  ``ff(aa) = hh(aa)`` is that lemma at ``aa``.
"""

import pytest

from unicode_logic_kit.atp.twee_check import (
    _equation_is_variant, _match, _matches_conjunct, _replace_at, _verify_rewrite,
    check_twee_proof, goal_mismatch, goal_matches_conclusion,
)
from unicode_logic_kit.atp.twee_entailment import (
    TweeAxiom, TweeChain, TweeCitation, TweeEquation, TweeGoal, TweeLemma, TweeProof,
)
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Function, Not, Number, Or, Quantifier, Variable,
)

_X, _Y = Variable("x"), Variable("y")
_BIG_X, _BIG_Y = Variable("X"), Variable("Y")
_AA, _BB, _CC, _KK = (Constant(name) for name in ("aa", "bb", "cc", "kk"))


def _app(name, *args):
    return Function(name, list(args))


def _eq(left, right):
    return Atom("=", [left, right])


def _all(variable, body):
    return Quantifier("∀", variable, body)


def _chain(*steps):
    """``_chain(t0, (kind, number, name, reversed), t1, ...)``: terms and citations alternate."""
    terms, citations = [steps[0]], []
    for citation, term in zip(steps[1::2], steps[2::2]):
        kind, number, name, reverse = citation
        citations.append(TweeCitation(kind, number, name, reverse))
        terms.append(term)
    return TweeChain(tuple(terms), tuple(citations))


def _axiom(number, name, lhs, rhs):
    return TweeAxiom(number, name, TweeEquation(lhs, rhs))


def _ax(number, name):
    return ("axiom", number, name, False)


def _lemma_ref(number):
    return ("lemma", number, None, False)


# ∀x ff(x) = gg(x),  ∀x gg(x) = hh(x)   ⊢   ff(aa) = hh(aa)
_PREMISES = [_all(_X, _eq(_app("ff", _X), _app("gg", _X))),
             _all(_X, _eq(_app("gg", _X), _app("hh", _X)))]
_CONCLUSION = _eq(_app("ff", _AA), _app("hh", _AA))
_FF_X, _GG_X, _HH_X = _app("ff", _BIG_X), _app("gg", _BIG_X), _app("hh", _BIG_X)
_AXIOMS = (_axiom(1, "premise_1", _FF_X, _GG_X), _axiom(2, "premise_2", _GG_X, _HH_X))


def _lemma(number=3, lhs=_FF_X, rhs=_HH_X, chain=None):
    """The lemma ``ff(X) = hh(X)``: ``ff(X)`` to ``gg(X)`` by axiom 1, to ``hh(X)`` by axiom 2."""
    chain = chain or _chain(_FF_X, _ax(1, "premise_1"), _GG_X, _ax(2, "premise_2"), _HH_X)
    return TweeLemma(number, TweeEquation(lhs, rhs), chain)


def _goal(lhs=_app("ff", _AA), rhs=_app("hh", _AA), chain=None, lemma_number=3):
    chain = chain or _chain(_app("ff", _AA), _lemma_ref(lemma_number), _app("hh", _AA))
    return TweeGoal(1, "goal", TweeEquation(lhs, rhs), chain)


def _proof(lemmas=None, goal=None, axioms=_AXIOMS):
    return TweeProof(axioms, (_lemma(),) if lemmas is None else tuple(lemmas), goal or _goal())


def test_the_proof_the_other_tests_start_from_is_accepted():
    proof = _proof()
    result = check_twee_proof(proof, _PREMISES)
    assert result.ok, result.error
    assert goal_mismatch(proof, _CONCLUSION) is None


# ---------------------------------------------------------------------------
# A chain proves the equation it states, and a lemma is used as the equation it states
# ---------------------------------------------------------------------------

def test_a_lemma_whose_chain_ends_elsewhere_than_its_stated_right_hand_side_is_refused():
    """The chain proves ``ff(X) = hh(X)``. Stated as ``ff(X) = kk(X)`` the lemma would let the
    goal ``ff(aa) = kk(aa)`` through, which does not follow: universe ``{0, 1}``, ``ff`` and
    ``gg`` and ``hh`` the identity, ``kk`` constantly 0 and ``aa`` ↦ 1 satisfy both premises
    and ``ff(aa) = 1 ≠ 0 = kk(aa)``."""
    stated = _app("kk", _BIG_X)
    wrong_goal = _goal(rhs=_app("kk", _AA),
                       chain=_chain(_app("ff", _AA), _lemma_ref(3), _app("kk", _AA)))
    proof = _proof(lemmas=[_lemma(rhs=stated)], goal=wrong_goal)
    result = check_twee_proof(proof, _PREMISES)
    assert not result.ok
    assert "lemma 3" in result.error and "does not end at its stated right-hand side" in result.error
    # the goal check cannot see the chain: it matches the wrong conclusion, so this is what refuses
    assert goal_matches_conclusion(proof, _eq(_app("ff", _AA), _app("kk", _AA))) is True


def test_a_lemma_whose_chain_starts_elsewhere_than_its_stated_left_hand_side_is_refused():
    """Stated as ``kk(X) = hh(X)`` the lemma lets ``kk(aa) = hh(aa)`` through: universe
    ``{0, 1}``, ``ff`` and ``gg`` and ``hh`` the identity, ``kk`` constantly 0, ``aa`` ↦ 1,
    so ``kk(aa) = 0 ≠ 1 = hh(aa)``."""
    wrong_goal = _goal(lhs=_app("kk", _AA),
                       chain=_chain(_app("kk", _AA), _lemma_ref(3), _app("hh", _AA)))
    proof = _proof(lemmas=[_lemma(lhs=_app("kk", _BIG_X))], goal=wrong_goal)
    result = check_twee_proof(proof, _PREMISES)
    assert not result.ok
    assert "lemma 3" in result.error and "does not start at its stated left-hand side" in result.error
    assert goal_matches_conclusion(proof, _eq(_app("kk", _AA), _app("hh", _AA))) is True


def test_a_goal_whose_chain_ends_elsewhere_than_its_stated_right_hand_side_is_refused():
    """The chain takes ``ff(aa)`` to ``hh(aa)``; the goal states ``ff(aa) = kk(aa)``, which does
    not follow (the countermodel of the lemma test above). The goal check sees only the
    stated equation, so it matches that conclusion and the chain check alone refuses."""
    proof = _proof(goal=_goal(rhs=_app("kk", _AA)))
    result = check_twee_proof(proof, _PREMISES)
    assert not result.ok
    assert result.error.startswith("goal: proof chain does not end at its stated right-hand side")
    assert goal_matches_conclusion(proof, _eq(_app("ff", _AA), _app("kk", _AA))) is True


def test_a_goal_whose_chain_starts_elsewhere_than_its_stated_left_hand_side_is_refused():
    proof = _proof(goal=_goal(lhs=_app("kk", _AA)))
    result = check_twee_proof(proof, _PREMISES)
    assert not result.ok
    assert result.error.startswith("goal: proof chain does not start at its stated left-hand side")
    assert goal_matches_conclusion(proof, _eq(_app("kk", _AA), _app("hh", _AA))) is True


# ---------------------------------------------------------------------------
# What a citation may point at
# ---------------------------------------------------------------------------

def _two_lemmas(first_number, second_number):
    """Two lemmas listed in this order: ``ff(X) = hh(X)`` (as ``first_number``) and
    ``ff(gg(X)) = hh(gg(X))`` (as ``second_number``), the second proved by the first at
    ``gg(X)``; the goal ``ff(gg(aa)) = hh(gg(aa))`` is the second at ``aa``."""
    first = _lemma(number=first_number)
    gg_x = _GG_X
    second = TweeLemma(
        second_number, TweeEquation(_app("ff", gg_x), _app("hh", gg_x)),
        _chain(_app("ff", gg_x), _lemma_ref(first_number), _app("hh", gg_x)))
    goal_lhs, goal_rhs = _app("ff", _app("gg", _AA)), _app("hh", _app("gg", _AA))
    goal = _goal(lhs=goal_lhs, rhs=goal_rhs,
                 chain=_chain(goal_lhs, _lemma_ref(second_number), goal_rhs))
    return _proof(lemmas=[first, second], goal=goal)


def test_a_lemma_may_cite_a_lemma_with_a_smaller_number():
    result = check_twee_proof(_two_lemmas(3, 5), _PREMISES)
    assert result.ok, result.error


def test_a_lemma_may_not_cite_a_lemma_with_a_greater_number_even_when_it_is_listed_before_it():
    """Twee numbers its lemmas in the order it derives them, so a lemma that cites one with a
    greater number is not a proof Twee printed."""
    result = check_twee_proof(_two_lemmas(5, 3), _PREMISES)
    assert not result.ok
    assert "cites lemma 5, which is not strictly earlier" in result.error


def test_a_lemma_may_not_cite_itself():
    self_citing = TweeLemma(3, TweeEquation(_FF_X, _HH_X),
                            _chain(_FF_X, _lemma_ref(3), _HH_X))
    result = check_twee_proof(_proof(lemmas=[self_citing]), _PREMISES)
    assert not result.ok
    assert "lemma 3" in result.error and "not an earlier proven lemma" in result.error


def test_a_citation_of_an_axiom_the_proof_never_states_is_refused():
    goal = _goal(chain=_chain(_app("ff", _AA), _ax(7, "premise_1"), _app("gg", _AA),
                              _ax(2, "premise_2"), _app("hh", _AA)))
    result = check_twee_proof(_proof(lemmas=[], goal=goal), _PREMISES)
    assert not result.ok
    assert "cites axiom 7, which was never stated" in result.error


def test_a_citation_names_the_axiom_it_was_stated_as():
    """Axiom 1 is ``premise_1``; a step that cites it as ``premise_2`` cites another premise."""
    goal = _goal(chain=_chain(_app("ff", _AA), _ax(1, "premise_2"), _app("gg", _AA),
                              _ax(2, "premise_2"), _app("hh", _AA)))
    result = check_twee_proof(_proof(lemmas=[], goal=goal), _PREMISES)
    assert not result.ok
    assert "cites axiom 1 as (premise_2)" in result.error and "stated as (premise_1)" in result.error


def test_a_goal_chain_that_cites_the_same_steps_without_a_lemma_is_accepted():
    goal = _goal(chain=_chain(_app("ff", _AA), _ax(1, "premise_1"), _app("gg", _AA),
                              _ax(2, "premise_2"), _app("hh", _AA)))
    assert check_twee_proof(_proof(lemmas=[], goal=goal), _PREMISES).ok


# ---------------------------------------------------------------------------
# A rewrite step changes ONE subterm, and only as the equation allows
# ---------------------------------------------------------------------------

def test_a_step_that_changes_a_second_place_is_not_a_rewrite_of_the_first():
    """``hh(ff(aa), cc)`` to ``hh(aa, dd)`` by ``ff(X) = X`` rewrites ``ff(aa)`` and also
    replaces ``cc`` by ``dd``, which no equation licenses."""
    term1 = _app("hh", _app("ff", _AA), _CC)
    assert _verify_rewrite(term1, _app("hh", _AA, _CC), _app("ff", _BIG_X), _BIG_X)
    assert not _verify_rewrite(term1, _app("hh", _AA, Constant("dd")), _app("ff", _BIG_X), _BIG_X)


def test_a_step_that_rewrites_to_a_term_the_equation_does_not_give_is_refused():
    """``ff(aa)`` is rewritten by ``ff(X) = gg(X)`` to ``gg(aa)``, not to ``gg(bb)``."""
    assert _verify_rewrite(_app("ff", _AA), _app("gg", _AA), _app("ff", _BIG_X), _app("gg", _BIG_X))
    assert not _verify_rewrite(_app("ff", _AA), _app("gg", _BB), _app("ff", _BIG_X),
                               _app("gg", _BIG_X))


def test_numbers_in_a_pattern_match_only_the_same_number():
    assert _match(Number(1), Number(1), {}) == {}
    assert _match(Number(1), Number(2), {}) is None
    assert _match(Number(1), Constant("a"), {}) is None


def test_the_numbers_of_a_restated_axiom_are_the_numbers_of_the_premise():
    premise = (_app("ff", Number(1)), Number(2))
    assert _equation_is_variant(premise, (_app("ff", Number(1)), Number(2)))
    assert not _equation_is_variant(premise, (_app("ff", Number(1)), Number(3)))
    assert not _equation_is_variant(premise, (_app("ff", Number(1)), Constant("2")))


# ---------------------------------------------------------------------------
# A restated axiom is the premise's equation under ONE renaming of its variables
# ---------------------------------------------------------------------------

def test_two_variables_of_the_premise_may_not_be_renamed_to_one():
    """The renaming is one-to-one: ``f(x, y) = x`` is not ``f(X, X) = X`` (the second is a
    special case of the first, and is the same equation only up to a renaming)."""
    premise = (_app("f", Variable("x"), Variable("y")), Variable("x"))
    assert _equation_is_variant(premise, (_app("f", _BIG_X, _BIG_Y), _BIG_X))
    assert not _equation_is_variant(premise, (_app("f", _BIG_X, _BIG_X), _BIG_X))


def test_one_variable_of_the_premise_may_not_be_renamed_to_two():
    """``f(x, x) = x`` is not ``f(X, Y) = X``: the second is MORE general than the premise."""
    premise = (_app("f", Variable("x"), Variable("x")), Variable("x"))
    assert not _equation_is_variant(premise, (_app("f", _BIG_X, _BIG_Y), _BIG_X))


# ---------------------------------------------------------------------------
# A premise is a universally quantified equation, or a conjunction of them
# ---------------------------------------------------------------------------

def _proof_by_the_identity_axiom(axiom_name="premise_1"):
    """The proof of ``ff(ff(cc)) = cc`` from the axiom ``ff(X) = X``."""
    ff_x = _app("ff", _BIG_X)
    ff_cc = _app("ff", _CC)
    goal_lhs = _app("ff", ff_cc)
    return TweeProof(
        (_axiom(1, axiom_name, ff_x, _BIG_X),), (),
        TweeGoal(1, "goal", TweeEquation(goal_lhs, _CC),
                 _chain(goal_lhs, _ax(1, axiom_name), ff_cc, _ax(1, axiom_name), _CC)))


_IDENTITY = _all(_X, _eq(_app("ff", _X), _X))


def test_the_proof_by_the_identity_axiom_is_accepted_for_the_universal_premise():
    proof = _proof_by_the_identity_axiom()
    assert check_twee_proof(proof, [_IDENTITY]).ok
    assert goal_mismatch(proof, _eq(_app("ff", _app("ff", _CC)), _CC)) is None


def test_an_existential_premise_does_not_give_the_axiom_of_a_universal_one():
    """``∃x ff(x) = x`` (a fixed point exists) is not ``∀x ff(x) = x``: universe ``{0, 1}``,
    ``ff(0) = 0`` and ``ff(1) = 0``, ``cc`` ↦ 1 satisfies it and ``ff(ff(cc)) = 0 ≠ 1``."""
    existential = Quantifier("∃", _X, _eq(_app("ff", _X), _X))
    for premise in (existential, And(_eq(_AA, _BB), existential)):
        result = check_twee_proof(_proof_by_the_identity_axiom(), [premise])
        assert not result.ok
        assert "invalid axioms argument" in result.error and "non-universal quantifier" in result.error


def test_an_existential_conclusion_is_refused_by_name():
    reason = goal_mismatch(_proof_by_the_identity_axiom(), Quantifier("∃", _X, _eq(_app("ff", _X), _X)))
    assert reason is not None and "non-universal quantifier" in reason
    assert goal_matches_conclusion(_proof_by_the_identity_axiom(),
                                   Quantifier("∃", _X, _eq(_app("ff", _X), _X))) is False


@pytest.mark.parametrize("premise", [
    Atom("R", [_AA, _BB]),                       # a predicate of two arguments is no equation
    Atom("=", [_AA]),                            # nor is an equality of one
    Atom("=", [_AA, _BB, _CC]),                  # or of three
    Or(_eq(_AA, _BB), _eq(_CC, _AA)),
    Not(_eq(_AA, _BB)),
], ids=["R(aa, bb)", "= of one", "= of three", "or", "not"])
def test_a_premise_that_is_not_an_equation_gives_no_axiom(premise):
    proof = TweeProof((_axiom(1, "premise_1", _AA, _BB),), (),
                      TweeGoal(1, "goal", TweeEquation(_AA, _BB),
                               _chain(_AA, _ax(1, "premise_1"), _BB)))
    result = check_twee_proof(proof, [premise])
    assert not result.ok
    assert "invalid axioms argument" in result.error and "not an equation" in result.error
    reason = goal_mismatch(proof, premise)
    assert reason is not None and "not an equation" in reason


# ---------------------------------------------------------------------------
# A free variable is one unknown element, wherever in an equation it sits
# ---------------------------------------------------------------------------

def test_a_variable_that_is_free_only_on_the_right_of_an_equation_is_still_free():
    """The premise ``aa = ff(x)`` with ``x`` free: the axiom ``aa = ff(X)`` of the proof proves
    ``aa = ff(bb)`` for every element, the premise only for the unknown ``x``: universe
    ``{0, 1}``, ``aa`` ↦ 0, ``x`` ↦ 0, ``ff`` the identity, ``bb`` ↦ 1."""
    premise = _eq(_AA, _app("ff", _X))
    goal_rhs = _app("ff", _BB)
    proof = TweeProof((_axiom(1, "premise_1", _AA, _app("ff", _BIG_X)),), (),
                      TweeGoal(1, "goal", TweeEquation(_AA, goal_rhs),
                               _chain(_AA, _ax(1, "premise_1"), goal_rhs)))
    result = check_twee_proof(proof, [premise])
    assert not result.ok and "free variable" in result.error
    assert check_twee_proof(proof, [_all(_X, premise)]).ok
    reason = goal_mismatch(proof, premise)
    assert reason is not None and "free variable" in reason

def test_a_variable_that_is_free_only_inside_a_function_is_still_free():
    """The premise ``ff(x) = aa`` with ``x`` free says something about ONE element. The axiom
    ``ff(X) = aa`` of the proof says it of every element and proves ``ff(bb) = aa``, which the
    premise does not: universe ``{0, 1}``, ``x`` ↦ 0, ``aa`` ↦ 0, ``ff`` the identity satisfy the
    premise (``ff(0) = 0``) and, with ``bb`` ↦ 1, ``ff(bb) = 1 ≠ 0``. The variable does not
    occur on its own anywhere, only as an argument."""
    premise = _eq(_app("ff", _X), _AA)
    goal_lhs = _app("ff", _BB)
    proof = TweeProof((_axiom(1, "premise_1", _app("ff", _BIG_X), _AA),), (),
                      TweeGoal(1, "goal", TweeEquation(goal_lhs, _AA),
                               _chain(goal_lhs, _ax(1, "premise_1"), _AA)))
    result = check_twee_proof(proof, [premise])
    assert not result.ok and "free variable" in result.error
    assert check_twee_proof(proof, [_all(_X, premise)]).ok
    reason = goal_mismatch(proof, premise)
    assert reason is not None and "free variable" in reason
    # closed, the same equation is the claim the proof's goal (at the fresh constant bb) proves
    assert goal_mismatch(proof, _all(_X, premise)) is None


# ---------------------------------------------------------------------------
# The Skolem constant of a goal is a name of nobody else's, on either side of each equation
# ---------------------------------------------------------------------------

def _ground_proof(axiom_lhs, axiom_rhs):
    """The proof of the premise ``axiom_lhs = axiom_rhs`` by itself."""
    return TweeProof((_axiom(1, "premise_1", axiom_lhs, axiom_rhs),), (),
                     TweeGoal(1, "goal", TweeEquation(axiom_lhs, axiom_rhs),
                              _chain(axiom_lhs, _ax(1, "premise_1"), axiom_rhs)))


def test_a_constant_that_only_the_left_of_an_axiom_has_is_not_a_fresh_constant():
    """Premise ``ff(aa) = hh(bb)``; the claim ``∀x ff(x) = hh(bb)`` does not follow: universe
    ``{0, 1}``, ``aa`` and ``bb`` ↦ 0, ``hh`` the identity, ``ff`` the identity satisfy the
    premise (0 = 0) and ``ff(1) = 1 ≠ 0 = hh(bb)``. ``aa`` is a symbol of the axiom's left side
    and of nothing else of the problem."""
    premise = _eq(_app("ff", _AA), _app("hh", _BB))
    proof = _ground_proof(_app("ff", _AA), _app("hh", _BB))
    claim = _all(_X, _eq(_app("ff", _X), _app("hh", _BB)))
    assert check_twee_proof(proof, [premise]).ok
    reason = goal_mismatch(proof, claim)
    assert reason is not None and "aa" in reason
    assert goal_mismatch(proof, premise) is None


def test_a_constant_that_only_the_right_of_an_axiom_has_is_not_a_fresh_constant():
    """Premise ``ff(bb) = hh(aa)``; the claim ``∀x ff(bb) = hh(x)`` does not follow: universe
    ``{0, 1}``, ``bb`` ↦ 0, ``aa`` ↦ 0, ``ff(0) = 0``, ``hh`` the identity satisfy the premise
    and ``hh(1) = 1 ≠ 0 = ff(bb)``."""
    premise = _eq(_app("ff", _BB), _app("hh", _AA))
    proof = _ground_proof(_app("ff", _BB), _app("hh", _AA))
    claim = _all(_X, _eq(_app("ff", _BB), _app("hh", _X)))
    assert check_twee_proof(proof, [premise]).ok
    reason = goal_mismatch(proof, claim)
    assert reason is not None and "aa" in reason
    assert goal_mismatch(proof, premise) is None


def test_a_constant_that_only_the_left_of_the_claim_has_is_not_a_fresh_constant():
    """Premise ``∀y ff(y, y) = gg(y)``; the claim ``∀x ff(kk, x) = gg(x)`` does not follow:
    universe ``{0, 1}``, ``kk`` ↦ 0, ``gg`` constantly 0, ``ff(0, 1) = 1`` and 0 elsewhere (the
    premise holds at 0 and at 1) and ``ff(kk, 1) = 1 ≠ 0 = gg(1)``. The goal is the claim at
    ``kk``, which the axiom proves; ``kk`` is a symbol of the claim's left side only."""
    premise = _all(_Y, _eq(_app("ff", _Y, _Y), _app("gg", _Y)))
    ff_yy = _app("ff", _BIG_X, _BIG_X)
    goal_lhs, goal_rhs = _app("ff", _KK, _KK), _app("gg", _KK)
    proof = TweeProof((_axiom(1, "premise_1", ff_yy, _app("gg", _BIG_X)),), (),
                      TweeGoal(1, "goal", TweeEquation(goal_lhs, goal_rhs),
                               _chain(goal_lhs, _ax(1, "premise_1"), goal_rhs)))
    claim = _all(_X, _eq(_app("ff", _KK, _X), _app("gg", _X)))
    assert check_twee_proof(proof, [premise]).ok
    reason = goal_mismatch(proof, claim)
    assert reason is not None and "kk" in reason


def test_a_constant_that_only_the_right_of_the_claim_has_is_not_a_fresh_constant():
    """Premise ``∀y gg(y) = ff(y, y)``; the claim ``∀x gg(x) = ff(kk, x)`` does not follow
    (the countermodel of the test above, the equations read from right to left)."""
    premise = _all(_Y, _eq(_app("gg", _Y), _app("ff", _Y, _Y)))
    goal_lhs, goal_rhs = _app("gg", _KK), _app("ff", _KK, _KK)
    proof = TweeProof((_axiom(1, "premise_1", _app("gg", _BIG_X), _app("ff", _BIG_X, _BIG_X)),), (),
                      TweeGoal(1, "goal", TweeEquation(goal_lhs, goal_rhs),
                               _chain(goal_lhs, _ax(1, "premise_1"), goal_rhs)))
    claim = _all(_X, _eq(_app("gg", _X), _app("ff", _KK, _X)))
    assert check_twee_proof(proof, [premise]).ok
    reason = goal_mismatch(proof, claim)
    assert reason is not None and "kk" in reason


def test_a_variable_matched_to_a_compound_term_or_to_a_taken_constant_is_no_skolem_constant():
    """The pieces of the goal check, called without the list that collects reasons."""
    compound = _app("gg", _AA)
    assert _matches_conjunct(_app("ff", _X), _X, _app("ff", compound), compound) is False
    assert _matches_conjunct(_app("ff", _X), _X, _app("ff", _AA), _AA, frozenset({"aa"})) is False
    assert _matches_conjunct(_app("ff", _X), _X, _app("ff", _AA), _AA) is True


def _paired_proof():
    """From ``∀y ff(y) = gg(y)`` and ``∀y hh(y) = kk(y)``: the goal ``pair(ff(sk), hh(tk)) =
    pair(gg(sk), kk(tk))``, which says ``ff(sk) = gg(sk)`` and ``hh(tk) = kk(tk)`` (``pair`` is
    the encoding of a conjunction, ``sk`` and ``tk`` the Skolem constants of its two slots)."""
    sk, tk = Constant("sk"), Constant("tk")
    start = _app("pair", _app("ff", sk), _app("hh", tk))
    middle = _app("pair", _app("gg", sk), _app("hh", tk))
    end = _app("pair", _app("gg", sk), _app("kk", tk))
    premises = [_all(_Y, _eq(_app("ff", _Y), _app("gg", _Y))),
                _all(_Y, _eq(_app("hh", _Y), _app("kk", _Y)))]
    proof = TweeProof(
        (_axiom(1, "premise_1", _app("ff", _BIG_X), _app("gg", _BIG_X)),
         _axiom(2, "premise_2", _app("hh", _BIG_X), _app("kk", _BIG_X))), (),
        TweeGoal(1, "goal", TweeEquation(start, end),
                 _chain(start, _ax(1, "premise_1"), middle, _ax(2, "premise_2"), end)))
    return proof, premises


def test_each_slot_of_an_encoded_goal_is_the_statement_of_one_conjunct():
    """The goal says two things, and a conclusion of two conjuncts is restated by it when each
    conjunct is one of the two. Two conjuncts that are both ``ff(x) = gg(x)`` are one statement
    written twice, which a goal of two different statements is not."""
    proof, premises = _paired_proof()
    assert check_twee_proof(proof, premises).ok
    both = And(_all(_X, _eq(_app("ff", _X), _app("gg", _X))),
               _all(_X, _eq(_app("hh", _X), _app("kk", _X))))
    assert goal_mismatch(proof, both) is None
    assert goal_mismatch(proof, And(both.right, both.left)) is None
    twice = And(_all(_X, _eq(_app("ff", _X), _app("gg", _X))),
                _all(_Y, _eq(_app("ff", _Y), _app("gg", _Y))))
    assert goal_mismatch(proof, twice) is not None


# ---------------------------------------------------------------------------
# The pieces a proof is checked with
# ---------------------------------------------------------------------------

def test_a_constant_of_the_premise_is_not_a_variable_of_the_restated_axiom_and_back():
    """``ff(aa) = aa`` and ``ff(X) = X`` are two equations: the second says it of every element."""
    constant_form = (_app("ff", _AA), _AA)
    variable_form = (_app("ff", _BIG_X), _BIG_X)
    assert _equation_is_variant(constant_form, constant_form)
    assert not _equation_is_variant(constant_form, variable_form)
    assert not _equation_is_variant(variable_form, constant_form)


def test_a_function_is_not_a_constant_of_the_same_name_in_either_direction():
    assert not _equation_is_variant((_app("ff", _AA), _AA), (Constant("ff"), _AA))
    assert not _equation_is_variant((Constant("ff"), _AA), (_app("ff", _AA), _AA))


def test_the_renaming_of_variables_holds_across_the_two_sides_of_an_equation():
    """``ff(x) = y`` is not ``ff(X) = X``: the restatement would be a special case (``y`` taken
    for ``x``), and the relation the checker names is the equation up to a renaming."""
    premise = (_app("ff", Variable("x")), Variable("y"))
    assert _equation_is_variant(premise, (_app("ff", _BIG_X), _BIG_Y))
    assert not _equation_is_variant(premise, (_app("ff", _BIG_X), _BIG_X))


def test_a_pattern_that_is_not_a_term_matches_nothing():
    assert _match(Atom("ff", [_BIG_X]), _app("ff", _AA), {}) is None
    assert _match(_app("ff", _BIG_X), _AA, {}) is None
    assert _match(_AA, _app("aa", _AA), {}) is None


def test_a_step_whose_position_does_not_exist_in_the_next_term_is_no_rewrite_of_it():
    """``ff(gg(aa))`` to ``ff(bb)`` by ``aa = bb``: ``aa`` sits at a depth ``ff(bb)`` does not reach."""
    assert not _verify_rewrite(_app("ff", _app("gg", _AA)), _app("ff", _BB), _AA, _BB)
    assert _verify_rewrite(_app("ff", _app("gg", _AA)), _app("ff", _app("gg", _BB)), _AA, _BB)


def test_a_rewrite_deep_in_the_second_argument_is_checked_at_its_own_position():
    term1 = _app("hh", _AA, _app("ff", _app("gg", _BB)))
    term2 = _app("hh", _AA, _app("ff", _CC))
    assert _verify_rewrite(term1, term2, _app("gg", _BB), _CC)
    assert _replace_at(term1, (1, 0, 0), _CC) == _app("hh", _AA, _app("ff", _app("gg", _CC)))
    assert _replace_at(term1, (), _CC) == _CC


def test_a_position_below_a_constant_cannot_be_replaced():
    with pytest.raises(ValueError, match="non-Function"):
        _replace_at(_AA, (0,), _BB)


def test_a_step_that_is_not_a_rewrite_names_what_it_cited_and_in_which_direction():
    wrong_direction = _goal(rhs=_app("gg", _AA), chain=_chain(
        _app("ff", _AA), ("axiom", 1, "premise_1", True), _app("gg", _AA)))
    error = check_twee_proof(_proof(lemmas=[], goal=wrong_direction), _PREMISES).error
    assert error.startswith("goal step 1:") and "axiom 1 (premise_1)" in error and error.endswith("R->L")
    wrong_result = _goal(rhs=_app("gg", _AA), chain=_chain(
        _app("ff", _AA), _lemma_ref(3), _app("gg", _AA)))
    error = check_twee_proof(_proof(goal=wrong_result), _PREMISES).error
    assert error.startswith("goal step 1:") and error.endswith("instance of lemma 3")
