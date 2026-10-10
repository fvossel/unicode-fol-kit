"""The classical parser modes are the combinations of three independent choices.

A classical mode is fixed by the order (first, second, third), by whether the modal
family is there, and by whether the individual binders and constants carry sorts:
twelve modes. These tests state what each combination accepts by ONE rule and check
it for every pair of modes, and they pin the four combinations that are built from
the same parts as their neighbours:

    second order + modal                     MSFLParser(second_order=True, modal=True)
    second order + modal + sorts             ... many_sorted=True
    third order + sorts                      MSFLParser(third_order=True, many_sorted=True)
    third order + modal + sorts              ... modal=True

The rule. A formula that uses the features ``(order, modal, sorted)`` is accepted by
the mode ``(order', modal', sorted')`` exactly when ``order <= order'``, the modal
family is there if the formula needs it, and ``sorted == sorted'``. The last is an
equality because a sorted mode refuses an unsorted binder and an unsorted mode has
no sort annotation.

The rule is about the syntax. The third-order modes also TYPE what they read, over
the whole formula, and refuse two binders of one name at two arities, which the
second-order modes accept; that one difference has a test of its own below.
"""

import itertools

import pytest

from unicode_logic_kit import (
    MSFLParser, MixedSlotError, NestedPropertySlotError, analyse_signatures,
)
from unicode_logic_kit.fol._fol_nodes import build_grammar, parser_ops_for_mode
from unicode_logic_kit.fol.msflparser import _REGISTRY_MODE
from unicode_logic_kit.fol.naming import NamingError, ParsingError
from unicode_logic_kit.fol.nodes import (
    Atom, Box, Cardinality, Constant, Contrast, Count, Measure, Nominal, PredicateTerm,
    SecondOrderQuantifier, SortedCardinality, SortedConstant, SortedCount, SortedQuantifier,
)
from unicode_logic_kit.fol._so_nodes import ConflictingArityError

ORDERS = (1, 2, 3)

#: (order, modal, sorted) -> the name the parser gives the mode.
MODE_NAMES = {
    (1, False, False): "fol",
    (1, False, True): "msfol",
    (1, True, False): "modal",
    (1, True, True): "modal_sorted",
    (2, False, False): "so",
    (2, False, True): "so_sorted",
    (2, True, False): "somodal",
    (2, True, True): "somodal_sorted",
    (3, False, False): "to",
    (3, False, True): "to_sorted",
    (3, True, False): "tomodal",
    (3, True, True): "tomodal_sorted",
}
COMBINATIONS = sorted(MODE_NAMES)


def flags(order, modal, many_sorted):
    kwargs = {}
    if order == 2:
        kwargs["second_order"] = True
    if order == 3:
        kwargs["third_order"] = True
    if modal:
        kwargs["modal"] = True
    if many_sorted:
        kwargs["many_sorted"] = True
    return kwargs


def parser(order, modal, many_sorted):
    return MSFLParser(**flags(order, modal, many_sorted))


def witness(order, modal, many_sorted):
    """A formula that uses every feature of the combination, and no other.

    One conjunct per feature: an individual quantifier (sorted or not), a predicate
    quantifier from the second order on, a predicate in argument position at the third,
    and a box if the modal family is there.
    """
    parts = ["(∀x:S Q(x))" if many_sorted else "(∀x Q(x))"]
    if order >= 2:
        parts.append("(∃P P)")
    if order == 3:
        parts.append("Pos(G)")
    if modal:
        parts.append("□R")
    return " ∧ ".join(parts)


@pytest.mark.parametrize("combination", COMBINATIONS)
def test_the_twelve_combinations_are_twelve_modes(combination):
    assert parser(*combination)._mode == MODE_NAMES[combination]


def test_every_mode_has_a_grammar_of_its_own_name():
    assert set(MODE_NAMES.values()) <= set(_REGISTRY_MODE)
    assert len(set(MODE_NAMES.values())) == 12


@pytest.mark.parametrize("formula_of, mode", list(itertools.product(COMBINATIONS, COMBINATIONS)))
def test_a_mode_accepts_exactly_the_formulas_of_the_modes_it_contains(formula_of, mode):
    text = witness(*formula_of)
    order, modal, many_sorted = formula_of
    mode_order, mode_modal, mode_sorted = mode
    accepted = order <= mode_order and (mode_modal or not modal) and many_sorted == mode_sorted
    if accepted:
        node = parser(*mode).parse(text)
        # what one mode accepts, every mode that contains it reads as the same formula
        assert node == parser(*formula_of).parse(text)
        assert node.to_unicode_str() == parser(*formula_of).parse(text).to_unicode_str()
    else:
        with pytest.raises((NamingError, ParsingError)):
            parser(*mode).parse(text)


# ---------------------------------------------------------------------------
# The four modes are built from the parts of their neighbours
# ---------------------------------------------------------------------------

def aliases(registry_mode):
    return {op.rule_alias for op in parser_ops_for_mode(registry_mode)}


def test_second_order_modal_has_the_operators_of_third_order_modal():
    """Same operators; the difference between the two is the argument layer alone."""
    assert aliases("second_order_modal") == aliases("modal") | aliases("second_order")
    assert aliases("second_order_modal") == aliases("third_order_modal")
    assert "hoarglist" in build_grammar("third_order_modal")
    assert "hoarglist" not in build_grammar("second_order_modal")


def test_a_sorted_mode_has_the_sorted_binders_and_no_unsorted_one():
    unsorted_binders = {"quantifier_", "count_"}
    expected = (aliases("msfol") | aliases("modal") | aliases("second_order")) - unsorted_binders
    assert aliases("second_order_modal_sorted") == expected
    assert aliases("third_order_modal_sorted") == expected
    assert aliases("third_order_sorted") == aliases("so_sorted")
    for registry_mode in ("second_order_modal_sorted", "third_order_sorted",
                          "third_order_modal_sorted"):
        assert not (aliases(registry_mode) & unsorted_binders)
        assert {"sorted_quantifier_", "sorted_const_"} <= aliases(registry_mode)


def test_the_third_order_sorted_modes_have_the_third_order_argument_layer():
    for registry_mode in ("third_order_sorted", "third_order_modal_sorted"):
        assert "hoarglist" in build_grammar(registry_mode)
    assert "hoarglist" not in build_grammar("second_order_modal_sorted")


# ---------------------------------------------------------------------------
# Second order + modal
# ---------------------------------------------------------------------------

MODAL_TEXTS = [
    "□(P → ◇Q)",
    "K_a P → P",
    "B_b (P ∧ Q) → B_b P",
    "Ⓖ(P → ⒻQ)",
    "ⓃP ∧ (P Ⓤ Q)",
    "ⓄP → ⓅP",
    "@i (P ∧ ◇j)",
    "□∀x (P(x) → Q(x))",
    "∃x ◇Likes(x, bob)",
    "◇⊤ → ¬□⊥",
]

SECOND_ORDER_TEXTS = [
    "∀P (P ∨ ¬P)",
    "∃P ∀x (P(x) ↔ Q(x))",
    "∀P (P(a) → P(b))",
    "∀x ∃P (P(x) ∧ ∀y (P(y) → Q(y, x)))",
    "∃R ∀x ∀y (R(x, y) → R(y, x))",
    "(∀P P(a)) ∧ (∃P P(a, b))",
]


@pytest.mark.parametrize("text", MODAL_TEXTS)
def test_second_order_modal_reads_a_modal_formula_as_the_modal_mode_does(text):
    assert (MSFLParser(second_order=True, modal=True).parse(text)
            == MSFLParser(modal=True).parse(text))


@pytest.mark.parametrize("text", SECOND_ORDER_TEXTS)
def test_second_order_modal_reads_a_second_order_formula_as_the_second_order_mode_does(text):
    assert (MSFLParser(second_order=True, modal=True).parse(text)
            == MSFLParser(second_order=True).parse(text))


def test_a_predicate_quantifier_over_a_box():
    node = MSFLParser(second_order=True, modal=True).parse("∀P (□P → P)")
    assert isinstance(node, SecondOrderQuantifier)
    assert (node.type, node.predicate, node.arity) == ("∀", "P", 0)
    assert isinstance(node.formula.left, Box)
    assert node.formula.left.formula == Atom("P", [])


def test_the_arity_of_a_bound_predicate_is_read_under_the_modal_operators():
    node = MSFLParser(second_order=True, modal=True).parse("∃P □◇K_a P(x, y)")
    assert node.arity == 2


def test_second_order_modal_infers_the_arity_per_binder():
    """Two binders of one name are two variables, as at second order. The third-order
    modes read names over the whole formula and refuse the same text."""
    text = "(∀P □P(a)) ∧ (∃P ◇P(a, b))"
    node = MSFLParser(second_order=True, modal=True).parse(text)
    assert node.left.arity == 1 and node.right.arity == 2
    with pytest.raises(ConflictingArityError):
        MSFLParser(third_order=True, modal=True).parse(text)


def test_a_bound_predicate_at_two_arities_is_refused():
    with pytest.raises(ConflictingArityError):
        MSFLParser(second_order=True, modal=True).parse("∀P (P(a) → □P(a, b))")


def test_a_predicate_in_argument_position_is_third_order():
    for kwargs in ({"second_order": True, "modal": True},
                   {"second_order": True, "modal": True, "many_sorted": True}):
        with pytest.raises(NamingError):
            MSFLParser(**kwargs).parse("□Pos(G)")


def test_a_free_agent_is_a_named_agent_in_every_modal_combination():
    """``K_a``: the agent ``a`` is the constant ``a`` unless a quantifier binds it."""
    plain = MSFLParser(modal=True).parse("K_a P")
    assert plain.agent == Constant("a")
    assert MSFLParser(second_order=True, modal=True).parse("K_a P") == plain
    assert MSFLParser(third_order=True, modal=True, many_sorted=True).parse("K_a P") == plain
    assert MSFLParser(second_order=True, modal=True, many_sorted=True).parse("K_a P") == plain


# ---------------------------------------------------------------------------
# Sorted individuals at second order with modal operators, and at third order
# ---------------------------------------------------------------------------

SORTED_MODAL_TEXTS = [
    "□∀x:Human Mortal(x)",
    "∃x:Human ◇Happy(x)",
    "K_a Mortal(socrates:Human)",
]

SORTED_SECOND_ORDER_TEXTS = [
    "∃P ∀x:S (P(x) ↔ Q(x))",
    "∀P (P(alice:Human) → P(alice:Human))",
]


@pytest.mark.parametrize("text", SORTED_MODAL_TEXTS)
def test_the_sorted_higher_order_modal_modes_read_a_sorted_modal_formula_alike(text):
    reference = MSFLParser(modal=True, many_sorted=True).parse(text)
    assert MSFLParser(second_order=True, modal=True, many_sorted=True).parse(text) == reference
    assert MSFLParser(third_order=True, modal=True, many_sorted=True).parse(text) == reference


@pytest.mark.parametrize("text", SORTED_SECOND_ORDER_TEXTS)
def test_the_sorted_higher_order_modes_read_a_sorted_second_order_formula_alike(text):
    reference = MSFLParser(second_order=True, many_sorted=True).parse(text)
    for kwargs in ({"second_order": True, "modal": True, "many_sorted": True},
                   {"third_order": True, "many_sorted": True},
                   {"third_order": True, "modal": True, "many_sorted": True}):
        assert MSFLParser(**kwargs).parse(text) == reference


@pytest.mark.parametrize("kwargs", [
    {"second_order": True, "modal": True, "many_sorted": True},
    {"third_order": True, "many_sorted": True},
    {"third_order": True, "modal": True, "many_sorted": True},
])
def test_a_sorted_mode_refuses_an_unsorted_binder_and_an_unsorted_constant(kwargs):
    p = MSFLParser(**kwargs)
    assert isinstance(p.parse("∀x:Human Mortal(x)"), SortedQuantifier)
    assert p.parse("Mortal(socrates:Human)").args[0] == SortedConstant("socrates", "Human")
    with pytest.raises(NamingError):
        p.parse("∀x Mortal(x)")
    with pytest.raises(NamingError):
        p.parse("Mortal(socrates)")


def test_the_predicate_quantifier_is_not_sorted():
    """``∀P`` is written without a sort in every mode; a sort after it is no syntax."""
    for kwargs in ({"second_order": True, "modal": True, "many_sorted": True},
                   {"third_order": True, "many_sorted": True}):
        p = MSFLParser(**kwargs)
        assert isinstance(p.parse("∀P ∀x:Human P(x)"), SecondOrderQuantifier)
        with pytest.raises((NamingError, ParsingError)):
            p.parse("∀P:Human ∀x:Human P(x)")


def test_third_order_over_sorted_individuals_keeps_the_typing_of_a_slot():
    """A slot holds an individual or a property; a sorted constant is an individual."""
    p = MSFLParser(third_order=True, many_sorted=True).parse
    node = p("∀x:Human ∃P (Pos(P) ∧ P(x) ∧ Ess(P, alice:Human))")
    slots = analyse_signatures([node]).slots
    assert slots == {"Pos": (("p", 1),), "P": ("i",), "Ess": (("p", 1), "i")}
    assert list(p("Pos(G)").args) == [PredicateTerm("G")]
    assert list(p("Ess(G, alice:Human)").args) == [PredicateTerm("G"),
                                                   SortedConstant("alice", "Human")]


def test_third_order_over_sorted_individuals_refuses_what_third_order_refuses():
    p = MSFLParser(third_order=True, many_sorted=True).parse
    with pytest.raises(MixedSlotError):
        p("Loves(alice:Human, bob:Human) ∧ Loves(alice:Human, G)")
    with pytest.raises(NestedPropertySlotError):
        p("Meta(Pos) ∧ Pos(G)")
    with pytest.raises(NamingError):
        p("□Pos(G)")                    # no modal family without modal=True


def test_a_lambda_argument_under_a_sorted_binder():
    p = MSFLParser(third_order=True, modal=True, many_sorted=True).parse
    node = p("∀x:Human □Pos(λy. ¬G(y))")
    assert node.to_unicode_str() == "∀x:Human □Pos(λy. ¬G(y))"


# ---------------------------------------------------------------------------
# What every mode owes: the printed text reads back, spans, serialisation
# ---------------------------------------------------------------------------

NEW_MODE_TEXTS = {
    "somodal": ["∀P (□P → P)", "∃P ∀x (P(x) ↔ ◇Q(x))", "K_a ∀P (P → P)", "@i ∃P P",
                "∀P ∃Q □(P ↔ ¬Q)", "∀P (P(a) → □P(a))"],
    "somodal_sorted": ["∀P □∀x:Human (P(x) → P(x))", "∃P P(alice:Human)",
                       "∀x:Human ∃P (P(x) ∧ □¬P(x))"],
    "to_sorted": ["Pos(G)", "∀P (Pos(P) → P(alice:Human))", "∀x:Human ∃P (P(x) ∧ Pos(P))",
                  "Pos(λx. ¬G(x))", "Ess(G, alice:Human)", "∃Z (Z(G) ∧ ¬Z(λx. ¬G(x)))"],
    "tomodal_sorted": ["∀P (Pos(P) → □Pos(P))", "∀x:Human □∃P (P(x) ∧ Pos(P))",
                       "∀P ∀x:Being (Ess(P, x) ↔ P(x) ∧ ∀Q (Q(x) → □∀y:Being (P(y) → Q(y))))"],
}
NEW_MODE_FLAGS = {
    "somodal": {"second_order": True, "modal": True},
    "somodal_sorted": {"second_order": True, "modal": True, "many_sorted": True},
    "to_sorted": {"third_order": True, "many_sorted": True},
    "tomodal_sorted": {"third_order": True, "modal": True, "many_sorted": True},
}
NEW_MODE_CASES = [(mode, text) for mode in sorted(NEW_MODE_TEXTS) for text in NEW_MODE_TEXTS[mode]]


@pytest.mark.parametrize("mode, text", NEW_MODE_CASES)
def test_the_printed_text_reads_back_as_the_same_formula(mode, text):
    p = MSFLParser(**NEW_MODE_FLAGS[mode])
    node = p.parse(text)
    assert p.parse(node.to_unicode_str()) == node


@pytest.mark.parametrize("mode, text", NEW_MODE_CASES)
def test_a_formula_survives_its_dictionary_form(mode, text):
    node = MSFLParser(**NEW_MODE_FLAGS[mode]).parse(text)
    assert type(node).from_dict(node.to_dict()) == node


@pytest.mark.parametrize("mode, text", NEW_MODE_CASES)
def test_parse_with_spans_builds_the_formula_parse_builds(mode, text):
    p = MSFLParser(**NEW_MODE_FLAGS[mode])
    spanned = p.parse_with_spans(text)
    assert spanned.formula == p.parse(text)
    extent = spanned.spans.for_node(spanned.formula).extent
    assert (extent.start, extent.end) == (0, len(text))


# ---------------------------------------------------------------------------
# A nominal as the body of a predicate quantifier
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("order, many_sorted", list(itertools.product((2, 3), (False, True))))
def test_in_a_modal_mode_a_nominal_can_be_the_body_of_a_predicate_quantifier(order, many_sorted):
    # A bare lower-case word in formula position names a world, and white space does not
    # separate a binder from its name: "∀ P(x)" is the binder ∀P and the body (x).
    p = parser(order, True, many_sorted)
    node = p.parse("∀ P(x)")
    assert node == SecondOrderQuantifier("∀", "P", 0, Nominal("x"))
    assert node == p.parse("∀P x")
    assert node.to_unicode_str() == "∀P x"


@pytest.mark.parametrize("order, many_sorted", list(itertools.product((2, 3), (False, True))))
def test_without_modal_operators_that_text_is_an_incomplete_formula(order, many_sorted):
    with pytest.raises(ParsingError, match="Incomplete formula"):
        parser(order, False, many_sorted).parse("∀ P(x)")


# ---------------------------------------------------------------------------
# The counting quantifier, the contrast connective, the measure and cardinality terms
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("order, modal", list(itertools.product(ORDERS, (False, True))))
def test_an_unsorted_mode_reads_the_four_forms_of_the_first_order_mode(order, modal):
    p = parser(order, modal, False)
    assert isinstance(p.parse("∃≥2 x P(x)"), Count)
    assert isinstance(p.parse("P(x) Ⓒ Q(x)"), Contrast)
    assert isinstance(p.parse("μ(x, height) > μ(y, height)").args[0], Measure)
    assert isinstance(p.parse("|{v : Votes(x, v)}| > |{v : Votes(y, v)}|").args[0], Cardinality)


@pytest.mark.parametrize("order, modal", list(itertools.product(ORDERS, (False, True))))
def test_a_sorted_mode_reads_the_counting_quantifier_and_the_contrast_connective(order, modal):
    p = parser(order, modal, True)
    assert isinstance(p.parse("∃≥2 x:S P(x)"), SortedCount)
    assert isinstance(p.parse("P(x) Ⓒ Q(x)"), Contrast)


def test_many_sorted_first_order_logic_reads_the_measure_and_the_cardinality_term():
    p = parser(1, False, True)
    assert isinstance(p.parse("μ(x, height:D) > μ(y, height:D)").args[0], Measure)
    assert isinstance(p.parse("|{v:S : Votes(x, v)}| > |{v:S : Votes(y, v)}|").args[0],
                      SortedCardinality)


@pytest.mark.parametrize("order, modal", [combination[:2] for combination in COMBINATIONS
                                          if combination[2] and combination[:2] != (1, False)])
def test_the_other_sorted_modes_have_no_measure_and_no_cardinality_term(order, modal):
    p = parser(order, modal, True)
    for text in ("μ(x, height:D) > μ(y, height:D)",
                 "|{v:S : Votes(x, v)}| > |{v:S : Votes(y, v)}|"):
        with pytest.raises(NamingError):
            p.parse(text)


# ---------------------------------------------------------------------------
# What stays refused
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("kwargs", [
    {"second_order": True, "modal": True, "fuzzy": True},
    {"second_order": True, "modal": True, "many_sorted": True, "fuzzy": True},
    {"third_order": True, "many_sorted": True, "fuzzy": True},
    {"third_order": True, "modal": True, "many_sorted": True, "fuzzy": True},
])
def test_the_classical_combinations_do_not_take_the_fuzzy_connectives(kwargs):
    with pytest.raises(ValueError, match="fuzzy"):
        MSFLParser(**kwargs)


def test_third_order_contains_second_order_in_every_combination():
    for extra in ({}, {"modal": True}, {"many_sorted": True},
                  {"modal": True, "many_sorted": True}):
        with pytest.raises(ValueError, match="already CONTAINS"):
            MSFLParser(third_order=True, second_order=True, **extra)
