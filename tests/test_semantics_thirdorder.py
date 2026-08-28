"""Third-order finite-model semantics: the level where an ARGUMENT can be a property.

The load-bearing test here is the differential against `satisfies_so`: a
second-order formula must get the same answer from both evaluators, in every
structure, or the third-order one has broken something on its way up. Everything
else pins what is genuinely new — property arguments, λ-extensions, and
quantification over predicates OF properties.
"""

import itertools

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol._ho_nodes import INDIVIDUAL
from unicode_fol_kit.semantics.secondorder import satisfies_so
from unicode_fol_kit.semantics.tarski import Structure
from unicode_fol_kit.semantics.thirdorder import (
    MAX_INTERPRETATIONS, all_interpretations, argument_value, holds_to,
    interpretation_count, satisfies_to, slot_values,
)
import unicode_fol_kit.semantics.thirdorder as thirdorder

SO = MSFLParser(second_order=True)
TO = MSFLParser(third_order=True)
TOM = MSFLParser(third_order=True, modal=True)


# --- the counting, before anything is enumerated ---------------------------

@pytest.mark.parametrize("n, expected", [(1, 2), (2, 4), (3, 8)])
def test_a_monadic_property_slot_ranges_over_every_subset(n, expected):
    assert len(slot_values(("p", 1), tuple(range(n)))) == expected


def test_an_individual_slot_ranges_over_the_domain():
    assert slot_values(INDIVIDUAL, (0, 1, 2)) == (0, 1, 2)


@pytest.mark.parametrize("signature, n, expected", [
    ((), 2, 2),                       # a proposition: false and true
    ((INDIVIDUAL,), 2, 4),            # a property of a 2-element domain
    ((INDIVIDUAL, INDIVIDUAL), 2, 16),
    ((("p", 1),), 2, 16),             # a predicate OF monadic properties
    ((("p", 1),), 3, 256),
])
def test_the_predicted_count_is_the_enumerated_count(signature, n, expected):
    domain = tuple(range(n))
    assert interpretation_count(signature, n) == expected
    assert len(list(all_interpretations(signature, domain))) == expected


def test_the_third_order_jump_is_where_the_cost_appears():
    """A property of 4 individuals: 16. A predicate of those properties: 2**16."""
    assert interpretation_count((INDIVIDUAL,), 4) == 16
    assert interpretation_count((("p", 1),), 4) == 65536
    assert interpretation_count((("p", 1),), 5) == 1 << 32


# --- the differential against the second-order evaluator -------------------

def _structures(domain, arities):
    """Every structure over ``domain`` interpreting each ``(name, arity)``."""
    tables = []
    for name, arity in arities:
        base = list(itertools.product(domain, repeat=arity))
        tables.append([
            (( name, arity), frozenset(base[i] for i in range(len(base))
                                       if (mask >> i) & 1))
            for mask in range(1 << len(base))
        ])
    for choice in itertools.product(*tables):
        yield Structure(domain, predicates=dict(choice))


SECOND_ORDER_CASES = [
    "∀P ∀x (P(x) ∨ ¬P(x))",
    "∃P ∀x P(x)",
    "∀P (∀x P(x) → ∃x P(x))",
    "∃P (P(u) ∧ ¬P(v))",
    "∀P ∃Q ∀x (P(x) ↔ ¬Q(x))",
    "∀P (∃x (P(x) ∧ R(x)) → ∃x R(x))",
    "∃P ∀x (P(x) ↔ R(x))",
    "∀x ∀y (R(x, y) → R(y, x))",
]


@pytest.mark.parametrize("text", SECOND_ORDER_CASES)
def test_the_two_evaluators_agree_on_every_second_order_formula_and_structure(text):
    """Third order must be a CONSERVATIVE extension: same verdict where both apply."""
    formula = SO.parse(text)
    domain = (0, 1)
    # Single lowercase letters parse as VARIABLES, so the two free names are
    # supplied by an assignment -- passed to BOTH evaluators, which is the point.
    assignment = {"u": 0, "v": 1}
    for structure in _structures(domain, [("R", 1), ("R", 2)]):
        assert (satisfies_to(formula, structure, assignment)
                == satisfies_so(formula, structure, assignment)), (
            text, structure.predicates)


# --- what is genuinely new -------------------------------------------------

DOMAIN = (0, 1)
G_EXTENSION = frozenset({(0,)})
#: G holds of 0 only, and G is the one positive property.
S = Structure(DOMAIN, predicates={("G", 1): {(0,)}, ("Pos", 1): {(G_EXTENSION,)}})


@pytest.mark.parametrize("text, expected", [
    ("Pos(G)", True),
    ("¬Pos(G)", False),
    ("∃P Pos(P)", True),
    ("∀P (Pos(P) → P(0))", True),      # the only positive property holds of 0
    ("∀P (Pos(P) → P(1))", False),
    ("∀P ∀Q (Pos(P) ∧ Pos(Q) → ∀x (P(x) ↔ Q(x)))", True),
])
def test_a_predicate_of_properties_is_evaluated_against_its_own_table(text, expected):
    assert holds_to(TO.parse(text), S) is expected


def test_a_lambda_argument_is_evaluated_to_its_extension():
    """``λx. x = 0`` picks out the same property as G, so it is positive too."""
    assert holds_to(TO.parse("Pos(λx. x = 0)"), S)
    assert not holds_to(TO.parse("Pos(λx. x = 1)"), S)
    assert argument_value(TO.parse("Pos(λx. x = 0)").args[0], S, {}, {},
                          thirdorder.analyse_signatures([TO.parse("Pos(G)")])) \
        == G_EXTENSION


def test_a_lambda_binder_shadows_an_outer_variable_of_the_same_name():
    """``x`` inside the λ is the λ's, not the quantifier's."""
    assert holds_to(TO.parse("∀x (G(x) → Pos(λx. x = 0))"), S)


def test_quantification_over_predicates_of_properties():
    """``∃Z`` ranges over the 16 predicates of monadic properties on this domain."""
    assert holds_to(TO.parse("∃Z (Z(G) ∧ ¬Z(λx. x = 1))"), S)
    assert holds_to(TO.parse("∀Z (Z(G) → Z(G))"), S)
    assert not holds_to(TO.parse("∀Z Z(G)"), S)


def test_an_unbound_predicate_argument_with_no_table_is_the_empty_relation():
    """First-order convention, unchanged: a missing table is the empty relation."""
    empty = Structure(DOMAIN, predicates={("Pos", 1): {(frozenset(),)}})
    assert holds_to(TO.parse("Pos(H)"), empty)


def test_a_propositional_binder_still_ranges_over_two_values():
    assert holds_to(TO.parse("∀Q (Q ∨ ¬Q)"), S)
    assert not holds_to(TO.parse("∀Q Q"), S)
    assert holds_to(TO.parse("∃Q Q"), S)


# --- the guard and the refusals --------------------------------------------

def test_an_impossible_enumeration_raises_instead_of_hanging():
    """Quantifying over predicates OF properties is where the space explodes.

    ``∀P Pos(P)`` on the same domain does NOT: P ranges over properties, which
    is only 2 ** 5. It is the THIRD-order binder that reaches 2 ** 32.
    """
    big = Structure(tuple(range(5)), predicates={("G", 1): {(0,)}})
    assert holds_to(TO.parse("∀P (P(0) ∨ ¬P(0))"), big)
    with pytest.raises(ValueError, match="MAX_INTERPRETATIONS"):
        holds_to(TO.parse("∀Z Z(G)"), big)


def test_the_cap_is_a_module_attribute_a_caller_can_raise():
    assert MAX_INTERPRETATIONS == thirdorder.MAX_INTERPRETATIONS


def test_a_modal_node_is_refused_by_name():
    with pytest.raises(NotImplementedError, match="Kripke"):
        holds_to(TOM.parse("□Pos(G)"), S)


def test_a_lambda_outside_argument_position_is_refused_by_name():
    from unicode_fol_kit.fol.nodes import Lambda, LambdaVar, Atom, Variable
    stray = Lambda(LambdaVar("x"), Atom("G", [Variable("x")]))
    with pytest.raises(NotImplementedError, match="argument position"):
        holds_to(stray, S)
