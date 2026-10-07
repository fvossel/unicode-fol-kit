"""Intuitionistic linear logic and the Lambek calculus read an atom over terms as one category and refuse
the rest of first-order syntax by name.

Both calculi are propositional: a sequent is built from categories by the calculus' own connectives, and
there are no individuals, no quantifiers, no counting and no identity.

* An ATOM OVER TERMS (``P(alpha)``, ``Loves(john, mary)``, a free variable included) is one category,
  identified by its predicate and its terms as written. That reading is sound in both directions, because a
  quantifier-free, equality-free sequent has no rule that substitutes one term for another: a first-order
  derivation of it IS a derivation between those categories, and so is the absence of one.
* A QUANTIFIER, a COUNTING or CARDINALITY node, a SORTED CONSTANT and an EQUALITY atom are not categories.
  Read as one, they answer about ANOTHER formula. By hand: ``∀x P(x) ⊢ P(alpha)`` is derivable in
  first-order linear logic (``∀L`` with the term ``alpha``, then the axiom ``P(alpha) ⊢ P(alpha)``) and has
  no derivation between the two categories ``∀x P(x)`` and ``P(alpha)``, so the category reading says
  "refuted" about a derivable sequent; ``⊢ alpha = alpha`` holds by reflexivity of identity and has no
  derivation between categories either.

The direct functions raise ``NotImplementedError`` naming the node, the calculus and what to do instead; the
backends answer UNKNOWN with reason ``unsupported`` and the same text, and ``api.prove`` carries it.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.lambek import lambek_derivable, lambek_prove
from unicode_logic_kit.atp.linear import ill_derivable, ill_prove
from unicode_logic_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, get_backend
from unicode_logic_kit.fol.nodes import (
    Atom, Cardinality, Constant, Count, Implies, LinearImplies, Number, Over, Product, Quantifier,
    SecondOrderQuantifier, SlashedExists, SortedCardinality, SortedConstant, SortedCount,
    SortedQuantifier, Tensor, Under, Variable,
)

X = Variable("x")
ALPHA, BETA = Constant("alpha"), Constant("beta")


def p(*args):
    return Atom("P", list(args))


def q(*args):
    return Atom("Q", list(args))


# One refused node per kind, each built by hand.
REFUSED = {
    "Quantifier": Quantifier("∀", X, p(X)),
    "SortedQuantifier": SortedQuantifier("∃", X, "Human", p(X)),
    "SecondOrderQuantifier": SecondOrderQuantifier("∃", "R", 0, Atom("R", [])),
    "SlashedExists": SlashedExists(X, ("y",), p(X)),
    "Count": Count("ge", Number(2), X, p(X)),
    "SortedCount": SortedCount("le", Number(1), X, "Human", p(X)),
    "Cardinality": Atom(">", [Cardinality(X, p(X)), Number(1)]),
    "SortedCardinality": Atom("=", [SortedCardinality(X, "Human", p(X)), Number(2)]),
    "SortedConstant": p(SortedConstant("carl", "Human")),
    "equality": Atom("=", [ALPHA, BETA]),
    "disequality": Atom("≠", [ALPHA, BETA]),
}
#: The class name a refusal of each kind names (an identity atom is an ``Atom``; the cardinality
#: terms are named through the term, not through the comparison around them).
NAMED = {name: ("Atom" if name in ("equality", "disequality") else name) for name in REFUSED}

CALCULI = {
    "ill": dict(prove=ill_prove, derivable=ill_derivable, calculus="intuitionistic linear logic",
                route="ill_prove", fuse=Tensor),
    "lambek": dict(prove=lambek_prove, derivable=lambek_derivable, calculus="the Lambek calculus",
                   route="lambek_prove", fuse=Product),
}


def _assert_names_node_and_calculus(message, node_class, calculus, route):
    assert message.startswith(route + ":")
    assert node_class in message
    assert calculus in message
    assert "first-order route" in message


# ---------------------------------------------------------------------------
# An atom over terms is one category
# ---------------------------------------------------------------------------

def test_ill_reads_atoms_over_terms_as_categories():
    # P(alpha) ⊸ Q(alpha), P(alpha) ⊢ Q(alpha): ⊸L with the two axioms.
    assert ill_derivable([LinearImplies(p(ALPHA), q(ALPHA)), p(ALPHA)], q(ALPHA))
    # P(alpha) ⊢ P(alpha) is the axiom; P(alpha) ⊢ P(beta) has no rule: the two atoms differ.
    assert ill_derivable([p(ALPHA)], p(ALPHA))
    assert not ill_derivable([p(ALPHA)], p(BETA))
    # P(alpha)⊗Q(alpha) ⊢ P(alpha) leaves Q(alpha) unused, which linear logic forbids.
    assert not ill_derivable([Tensor(p(ALPHA), q(ALPHA))], p(ALPHA))


def test_a_free_variable_is_a_parameter_and_the_atom_stays_a_category():
    y = Variable("y")
    assert ill_derivable([p(X)], p(X))
    assert not ill_derivable([p(X)], p(y))
    assert lambek_derivable([p(X)], p(X))
    assert not lambek_derivable([p(X)], p(y))


def test_comparison_atoms_over_numerals_are_categories_and_one_numeral_is_one_constant():
    # `<` is an uninterpreted binary predicate: 1 < 2 ⊢ 1 < 2 is the axiom, ⊢ 1 < 2 has no derivation.
    less = Atom("<", [Number(1), Number(2)])
    assert ill_derivable([less], less)
    assert not ill_derivable([], less)
    assert lambek_derivable([less], less)
    # Number(1) and Number(1.0) are one constant, so P(1) ⊢ P(1.0) is the axiom.
    assert ill_derivable([p(Number(1))], p(Number(1.0)))


def test_lambek_reads_atoms_over_terms_in_order():
    a, b = Atom("A", [ALPHA]), Atom("B", [ALPHA])
    # A, A\B ⊢ B (\L); the other order has no derivation: the calculus has no exchange.
    assert lambek_derivable([a, Under(a, b)], b)
    assert not lambek_derivable([Under(a, b), a], b)
    # B/A, A ⊢ B (/L).
    assert lambek_derivable([Over(b, a), a], b)


@pytest.mark.parametrize("backend", ["ill", "lambek"])
def test_the_backends_decide_atoms_over_terms(backend):
    if backend == "ill":
        premises, goal = [LinearImplies(p(ALPHA), q(ALPHA)), p(ALPHA)], q(ALPHA)
        refuted_goal = q(BETA)
    else:
        premises, goal = [p(ALPHA), Under(p(ALPHA), q(ALPHA))], q(ALPHA)
        refuted_goal = q(BETA)
    assert get_backend(backend).decide(goal, premises).status == PROVED
    verdict = get_backend(backend).decide(refuted_goal, premises)
    assert verdict.status == REFUTED


# ---------------------------------------------------------------------------
# Quantifiers, counts, cardinalities, sorted constants and identity are refused by name
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("calculus", sorted(CALCULI))
@pytest.mark.parametrize("kind", sorted(REFUSED))
def test_the_direct_functions_refuse_the_node_by_name(calculus, kind):
    calc, node = CALCULI[calculus], REFUSED[kind]
    plain = p(ALPHA)
    for call in (calc["prove"], calc["derivable"]):
        for antecedent, goal in (([node], plain), ([plain], node), ([plain, plain], calc["fuse"](plain, node))):
            with pytest.raises(NotImplementedError) as raised:
                call(antecedent, goal)
            _assert_names_node_and_calculus(str(raised.value), NAMED[kind], calc["calculus"], calc["route"])


@pytest.mark.parametrize("calculus", sorted(CALCULI))
def test_the_universal_instance_is_refused_and_not_answered_refuted(calculus):
    # ∀x P(x) ⊢ P(alpha) holds in first-order linear logic; the category reading would answer "no derivation".
    calc = CALCULI[calculus]
    with pytest.raises(NotImplementedError, match="Quantifier"):
        calc["derivable"]([REFUSED["Quantifier"]], p(ALPHA))
    verdict = get_backend(calculus).decide(p(ALPHA), [REFUSED["Quantifier"]])
    assert verdict.status == UNKNOWN and verdict.reason == "unsupported"


@pytest.mark.parametrize("calculus", sorted(CALCULI))
@pytest.mark.parametrize("kind", sorted(REFUSED))
def test_the_backends_answer_unsupported_with_the_node_named(calculus, kind):
    node = REFUSED[kind]
    plain = p(ALPHA)
    for premises, goal in (([node], plain), ([plain], node)):
        verdict = get_backend(calculus).decide(goal, premises)
        assert verdict.status == UNKNOWN and verdict.reason == "unsupported"
        assert NAMED[kind] in verdict.detail
        if kind in ("equality", "disequality"):
            assert kind + " atom" in verdict.detail
        assert CALCULI[calculus]["calculus"] in verdict.detail
        assert "first-order route" in verdict.detail
        assert verdict.countermodel is None


@pytest.mark.parametrize("calculus", sorted(CALCULI))
def test_through_api_prove_the_refusal_names_the_node(calculus):
    # A first-order entailment that is valid in every first-order reading: ∀x (P(x) → Q(x)), P(alpha) ⊢ Q(alpha).
    premises = [Quantifier("∀", X, Implies(p(X), q(X))), p(ALPHA)]
    verdict = api.prove(q(ALPHA), premises, backends=[calculus], logic=calculus)
    assert verdict.status == UNKNOWN
    assert "Quantifier" in verdict.detail and "unsupported" in verdict.detail


@pytest.mark.parametrize("calculus", sorted(CALCULI))
def test_an_equality_that_holds_a_cardinality_is_reported_through_the_cardinality(calculus):
    # `|{x : P(x)}| = 2` is an equality atom around a cardinality term; the term says more.
    node = Atom("=", [Cardinality(X, p(X)), Number(2)])
    verdict = get_backend(calculus).decide(p(ALPHA), [node])
    assert verdict.status == UNKNOWN and "Cardinality" in verdict.detail


def test_a_long_node_is_quoted_shortened():
    body = p(X)
    for i in range(40):
        body = Implies(body, q(Variable(f"v{i}")))
    node = Quantifier("∀", X, body)
    with pytest.raises(NotImplementedError) as raised:
        ill_prove([node], p(ALPHA))
    assert "…" in str(raised.value)
    assert node.to_unicode_str() not in str(raised.value)


# ---------------------------------------------------------------------------
# An empty antecedent is an answer, not an exception, at the backend
# ---------------------------------------------------------------------------

def test_the_lambek_backend_answers_unsupported_for_an_empty_premise_list():
    goal = p(ALPHA)
    verdict = get_backend("lambek").decide(goal, [])
    assert verdict.status == UNKNOWN and verdict.reason == "unsupported"
    assert "empty antecedent" in verdict.detail


def test_through_api_prove_an_empty_premise_list_is_unknown_and_says_why():
    verdict = api.prove(p(ALPHA), [], backends=["lambek"], logic="lambek")
    assert verdict.status == UNKNOWN
    assert "unsupported" in verdict.detail and "empty antecedent" in verdict.detail


def test_the_direct_function_still_raises_for_an_empty_sequence():
    with pytest.raises(ValueError, match="nonempty"):
        lambek_prove([], p(ALPHA))


def test_the_ill_backend_has_an_empty_antecedent_and_decides_it():
    # ⊢ A⊸A is derivable (⊸R then the axiom): ILL has sequents with an empty antecedent.
    a = Atom("A", [])
    assert get_backend("ill").decide(LinearImplies(a, a), []).status == PROVED
