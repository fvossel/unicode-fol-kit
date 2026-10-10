"""The bounded Kripke search on formulas with predicate quantifiers.

``modal_enum_search`` hands every candidate model to ``satisfies_modal``, which
interprets ``∀P`` / ``∃P``. So a formula with a propositional quantifier is searched on
the frames of a system, and the frame conditions of correspondence theory decide
what comes out: ``∀P (□P → P)`` says "this world sees itself", has a countermodel
among all frames and none among the reflexive ones.

The numbers of candidates below are the numbers of relations of a kind on one, two and
three worlds. A closed formula without free atoms has one valuation per frame, so the
search of a system looks at exactly that many candidates:

    reflexive              1 +  4 +  64 =  69
    transitive             2 + 13 + 171 = 186
    reflexive, transitive  1 +  4 +  29 =  34
    symmetric              2 +  8 +  64 =  74
    serial                 1 +  9 + 343 = 353
    all                    2 + 16 + 512 = 530
"""

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.kripke_enum import (
    KripkeEnumBackend, _collect, _terms_under_bound_predicates, modal_enum_search,
)
from unicode_logic_kit.atp.protocol import REFUTED, UNKNOWN
from unicode_logic_kit.semantics.kripke import satisfies_modal

SOM = MSFLParser(second_order=True, modal=True).parse
SOMS = MSFLParser(second_order=True, modal=True, many_sorted=True).parse


# (formula, system, worlds of the smallest countermodel or None, candidates looked at)
#
# The smallest countermodels, by hand:
#   ∀P (□P → P)     one world that does not see itself.
#   ∀P (□P → □□P)   two worlds: 0 sees 1, 1 sees 0, 0 does not see itself.
#   ∀P (P → □◇P)    two worlds: 0 sees 1 and 1 does not see 0. One world is not enough:
#                   a world that sees only itself is seen by its successor.
#   ∀P (□P → ◇P)    one world without a successor.
#   ∀P (◇P → □P)    two successors are needed, so two worlds.
SEARCHES = [
    ("∀P (□P → P)", "K", 1, None),
    ("∀P (□P → P)", "T", None, 69),
    ("∀P (□P → □□P)", "K", 2, None),
    ("∀P (□P → □□P)", "K4", None, 186),
    ("∀P (□P → □□P)", "S4", None, 34),
    ("∀P (P → □◇P)", "K", 2, None),
    ("∀P (P → □◇P)", "KB", None, 74),
    ("∀P (□P → ◇P)", "K", 1, None),
    ("∀P (□P → ◇P)", "D", None, 353),
    ("∀P (◇P → □P)", "K", 2, None),
    # Every world is the one world of some proposition: P = {this world}. Whatever
    # holds here then holds wherever P does.
    ("∃P (P ∧ ∀Q (Q → □(P → Q)))", "K", None, 530),
]


@pytest.mark.parametrize("text, frame, worlds, candidates", SEARCHES)
def test_the_search_finds_what_the_frame_condition_says(text, frame, worlds, candidates):
    formula = SOM(text)
    result = modal_enum_search(formula, frame=frame, max_worlds=3)
    assert result.unsupported is None
    if worlds is None:
        assert result.model is None and result.exhausted
        assert result.checked == candidates
    else:
        assert result.model is not None and not result.exhausted
        assert len(result.model.worlds) == worlds
        assert satisfies_modal(formula, result.model, 0) is False


def test_a_formula_without_a_modal_operator_has_one_frame_per_size():
    """No relation is built for a family the formula does not use: three candidates."""
    result = modal_enum_search(SOM("∀P (P ∨ ¬P)"), max_worlds=3)
    assert result.exhausted and result.checked == 3
    refuted = modal_enum_search(SOM("∃P (P ∧ ¬P)"), max_worlds=3)
    assert refuted.model is not None and refuted.checked == 1


def test_a_bound_atom_is_not_a_key_of_the_valuation():
    assert _collect(SOM("∀P (□P → P)")) == ((), ("alethic",))
    assert _collect(SOM("∀P (P(a) → □P(a))")) == ((), ("alethic",))
    assert _collect(SOM("∀P (P → Q)")) == (("Q",), ())


def test_a_free_occurrence_of_a_bound_name_is_a_key():
    """``P ∧ ∃P ¬P``: the first P is the model's own, and the search varies it. With P
    false at world 0 the conjunction is false."""
    formula = SOM("P ∧ ∃P ¬P")
    assert _collect(formula) == (("P",), ())
    result = modal_enum_search(formula)
    assert result.model is not None
    assert result.model.atoms_true_at(0) == frozenset()
    # ... and the bound occurrence is not varied: Q → ∃P (P ↔ Q) has no countermodel.
    valid = modal_enum_search(SOM("Q → ∃P (P ↔ Q)"), max_worlds=2)
    assert valid.exhausted and valid.checked == 2 + 4


def test_a_bound_predicate_of_one_term_is_searched():
    """One term is one individual: the atom ``P(a)`` is a proposition of each world.
    ``∀P (P(a) → □P(a))`` fails where the world has a successor other than itself."""
    formula = SOM("∀P (P(a) → □P(a))")
    assert _terms_under_bound_predicates(formula) == ("a",)
    result = modal_enum_search(formula)
    assert result.unsupported is None
    assert len(result.model.worlds) == 2
    assert satisfies_modal(formula, result.model, 0) is False


@pytest.mark.parametrize("text, named", [
    ("∃P (P(a) ∧ ¬P(b))", ("a", "b")),
    ("∀P (P(a) → P(b))", ("a", "b")),
    ("∀P ∃Q (P(a) ↔ Q(b))", ("a", "b")),
    ("∃R (R(a, b) ∧ ¬R(b, a))", ("a", "b")),
    ("∀P (P(f(a)) → □P(a))", ("a", "f(a)")),
])
def test_bound_predicates_of_two_terms_are_outside_the_search(text, named):
    """``∃P (P(a) ∧ ¬P(b))`` is false in a model in which ``a`` and ``b`` name one
    individual. A candidate of this search names an individual by its term, so no
    candidate is such a model, and "no countermodel" would be wrong."""
    formula = SOM(text)
    assert _terms_under_bound_predicates(formula) == named
    result = modal_enum_search(formula)
    assert result.model is None and not result.exhausted and result.checked == 0
    assert result.unsupported.startswith("NotImplementedError")
    assert named[0] in result.unsupported and named[1] in result.unsupported


def test_two_terms_under_free_predicates_do_not_matter():
    """Only a bound predicate can tell two terms apart; ``Q(a) ∧ ¬Q(b)`` next to a
    quantifier over a proposition is searched as before."""
    formula = SOM("∀P (P → P) ∧ (Q(a) → Q(b))")
    assert _terms_under_bound_predicates(formula) == ()
    result = modal_enum_search(formula)
    assert result.unsupported is None and result.model is not None
    assert result.model.atoms_true_at(0) == frozenset({"Q(a)"})


def test_a_sorted_constant_under_a_bound_predicate():
    """``c:S`` is the constant ``c``; its membership ``S(c)`` is fixed true and not varied."""
    formula = SOMS("∀P (P(socrates:Human) → □P(socrates:Human))")
    result = modal_enum_search(formula)
    assert result.unsupported is None
    assert len(result.model.worlds) == 2
    assert all("Human(socrates)" in result.model.atoms_true_at(w) for w in result.model.worlds)


def test_the_backend_reports_a_refutation_and_a_bound():
    backend = KripkeEnumBackend()
    refuted = backend.decide(SOM("∀P (□P → P)"))
    assert refuted.status == REFUTED
    assert refuted.countermodel["kind"] == "kripke"
    bounded = backend.decide(SOM("∀P (□P → P)"), frame="T")
    assert bounded.status == UNKNOWN and bounded.reason == "bound_hit"
    outside = backend.decide(SOM("∃P (P(a) ∧ ¬P(b))"))
    assert outside.status == UNKNOWN and outside.reason == "unsupported"


def test_a_premise_is_folded_into_the_goal_under_the_quantifier_reading():
    """From ``∀P (□P → P)`` (this world sees itself) ``□Q → Q`` follows; from
    ``∀P (□P → □□P)`` it does not."""
    backend = KripkeEnumBackend()
    follows = backend.decide(SOM("□Q → Q"), [SOM("∀P (□P → P)")], max_worlds=2)
    assert follows.status == UNKNOWN and follows.reason == "bound_hit"
    fails = backend.decide(SOM("□Q → Q"), [SOM("∀P (□P → □□P)")], max_worlds=2)
    assert fails.status == REFUTED
