"""The third-order modes: a predicate in argument position, and what it costs.

Third order is not "second order plus another quantifier". Second-order syntax
binds a predicate variable but still only ever APPLIES it (``∀P … P(x) …``);
third-order syntax puts a predicate in an ARGUMENT slot — ``Positive(G)``,
``Essence(G, x)``, ``Positive(λx. ¬G(x))``. That is a change to the argument
layer, and these tests pin the three things it brings with it: the node
(:class:`PredicateTerm`), the two modes (classical ``third_order``, and
``third_order`` + ``modal``), and the signature analysis that has to infer what
each argument slot holds because the surface syntax does not say.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Atom, Lambda, LambdaVar, Node, PredicateTerm, SecondOrderQuantifier,
    analyse_signatures, MixedSlotError,
)
from unicode_fol_kit.fol._fol_nodes import build_grammar, parser_ops_for_mode
from unicode_fol_kit.fol._ho_nodes import INDIVIDUAL, has_property_argument
from unicode_fol_kit.fol._so_nodes import ConflictingArityError
from unicode_fol_kit.fol.naming import NamingError, ParsingError

TO = MSFLParser(third_order=True)
TOM = MSFLParser(third_order=True, modal=True)
SO = MSFLParser(second_order=True)
MODAL = MSFLParser(modal=True)


# --- the mode itself --------------------------------------------------------

def test_argument_position_is_what_the_lower_modes_cannot_reach():
    """The one formula that separates the orders, refused by both lower modes."""
    text = "∀P (Pos(P) → P(x))"
    assert TO.parse(text) is not None
    with pytest.raises((NamingError, ParsingError)):
        SO.parse(text)          # binds P, but cannot pass it
    with pytest.raises((NamingError, ParsingError)):
        MODAL.parse(text)       # cannot even bind it


def test_classical_third_order_refuses_modal_operators():
    """``third_order`` alone is CLASSICAL; the box needs modal=True with it."""
    with pytest.raises((NamingError, ParsingError)):
        TO.parse("∀P (Pos(P) → □Pos(P))")
    assert TOM.parse("∀P (Pos(P) → □Pos(P))") is not None


def test_third_order_does_not_combine_with_second_order():
    """It CONTAINS second-order syntax, so asking for both is a category error."""
    with pytest.raises(ValueError, match="already CONTAINS"):
        MSFLParser(third_order=True, second_order=True)


@pytest.mark.parametrize("kwargs", [
    {"third_order": True, "many_sorted": True},
    {"third_order": True, "fuzzy": True},
])
def test_third_order_refuses_the_sorted_and_fuzzy_flags(kwargs):
    with pytest.raises(ValueError):
        MSFLParser(**kwargs)


def test_the_modes_are_their_base_modes_over_a_widened_argument_layer():
    """The clone is the whole mechanism: same operators, one different slot.

    If this ever fails, an operator was registered for ``modal`` or
    ``second_order`` without reaching the third-order modes — which is exactly
    the drift the cloning exists to prevent.
    """
    def ops(mode):
        return {(op.level, op.rule_alias, op.grammar, op.only_name)
                for op in parser_ops_for_mode(mode)}

    assert ops("third_order") == ops("second_order")
    assert ops("third_order_modal") == ops("modal") | ops("second_order")


def test_only_the_third_order_grammars_widen_the_argument_layer():
    """Every other mode's predicate application still takes a plain termlist."""
    for mode in ("fol", "msfol", "msfl", "fl", "modal", "second_order",
                 "dependence", "linear", "lambek"):
        grammar = build_grammar(mode)
        assert "hoarglist" not in grammar, mode
    for mode in ("third_order", "third_order_modal"):
        grammar = build_grammar(mode)
        assert 'PREDICATE "(" hoarglist ")"' in grammar
        assert "-> pred_arg_" in grammar


# --- the node ---------------------------------------------------------------

def test_a_predicate_argument_is_not_a_nullary_atom():
    """``Positive(G)`` is about the PROPERTY G, not about the proposition G."""
    parsed = TO.parse("Pos(G)")
    assert parsed == Atom("Pos", [PredicateTerm("G")])
    assert parsed != Atom("Pos", [Atom("G", [])])


def test_lambda_arguments_survive_and_carry_their_binder():
    parsed = TO.parse("Pos(λx. ¬P(x))")
    assert isinstance(parsed, Atom) and parsed.predicate == "Pos"
    (arg,) = parsed.args
    assert isinstance(arg, Lambda)
    assert arg.param == LambdaVar("x")


@pytest.mark.parametrize("text", [
    "Pos(G)",
    "Pos(λx. ¬P(x))",
    "Ess(G, a)",
    "∀P (Pos(P) ↔ ¬Pos(λx. ¬P(x)))",
    "∀P ∀x (Ess(P, x) ↔ P(x) ∧ ∀Q (Q(x) → ∀y (P(y) → Q(y))))",
])
def test_unicode_roundtrip(text):
    """Rendered back and re-parsed to the SAME node -- the kit's standing guarantee."""
    node = TO.parse(text)
    assert TO.parse(node.to_unicode_str()) == node


def test_latex_renders_a_predicate_argument():
    assert "Pos(G)" in TO.parse("Pos(G)").to_latex().replace("\\", "")
    assert "Ess(G, a)" in TO.parse("Ess(G, a)").to_latex().replace("\\", "")


def test_serialisation_roundtrip():
    node = TO.parse("Ess(G, a) ∧ Pos(λx. ¬G(x))")
    assert Node.from_dict(node.to_dict()) == node


@pytest.mark.parametrize("method", ["to_z3", "to_prover9", "to_tptp"])
def test_first_order_backends_refuse_a_property_argument(method):
    """Refused BY NAME, like second-order quantification -- not silently dropped."""
    with pytest.raises(NotImplementedError, match="third order"):
        getattr(PredicateTerm("G"), method)()


# --- the signature analysis -------------------------------------------------

def test_arity_propagates_across_formulas_not_just_within_one():
    """``Positive(G)`` says nothing alone; with ``G(x)`` elsewhere it says 1."""
    alone = analyse_signatures([TO.parse("Pos(G)")])
    assert alone.slots["Pos"] == (("p", 1),)
    assert alone.defaulted == frozenset({("Pos", 0)})

    together = analyse_signatures([TO.parse("Pos(G)"), TO.parse("G(a, b)")])
    assert together.arity["G"] == 2
    assert together.slots["Pos"] == (("p", 2),)
    assert together.defaulted == frozenset()


def test_a_lambda_argument_fixes_its_slot_by_binder_depth():
    signatures = analyse_signatures([TO.parse("Pos(λx. λy. R(x, y))")])
    assert signatures.slots["Pos"] == (("p", 2),)
    assert signatures.defaulted == frozenset()


def test_mixed_argument_slots_are_a_type_error_at_parse_time():
    """One slot holds an individual or a property. Never both."""
    with pytest.raises(MixedSlotError, match="slot 1 of 'Loves'"):
        TO.parse("Loves(x, y) ∧ Loves(x, G)")


def test_conflicting_application_arities_still_raise():
    with pytest.raises(ConflictingArityError):
        TO.parse("P(x) ∧ P(x, y)")


def test_essence_is_typed_as_a_property_and_an_individual():
    signatures = analyse_signatures([
        TO.parse("∀P ∀x (Ess(P, x) ↔ P(x))"),
    ])
    assert signatures.slots["Ess"] == (("p", 1), INDIVIDUAL)
    assert signatures.is_third_order()
    assert signatures.property_slots() == [("Ess", 0, 1)]


def test_a_purely_first_order_formula_is_not_third_order():
    signatures = analyse_signatures([TO.parse("∀x (P(x) → Q(x))")])
    assert not signatures.is_third_order()
    assert signatures.property_slots() == []


# --- the bound variable's arity --------------------------------------------

def _bound(node, acc=None):
    acc = [] if acc is None else acc
    if isinstance(node, SecondOrderQuantifier):
        acc.append((node.predicate, node.arity))
    for child in node._child_nodes():
        _bound(child, acc)
    return acc


def test_a_binder_used_only_in_argument_position_is_a_property_not_a_proposition():
    """``∀P (Pos(P) → □Pos(P))`` never applies P; arity 0 would retype the axiom."""
    assert _bound(TOM.parse("∀P (Pos(P) → □Pos(P))")) == [("P", 1)]


def test_a_binder_that_is_applied_takes_its_arity_from_the_application():
    assert _bound(TO.parse("∀P (Pos(P) → P(x, y))")) == [("P", 2)]


def test_an_unapplied_second_order_binder_is_still_propositional():
    """The default is about ARGUMENT position, and does not leak into plain SOL."""
    assert _bound(SO.parse("∀P (P → P)")) == [("P", 0)]
    assert _bound(TO.parse("∀P (P → P)")) == [("P", 0)]


def test_the_second_order_path_is_taken_when_there_is_no_property_argument():
    assert not has_property_argument(SO.parse("∀P ∀x (P(x) ∨ ¬P(x))"))
    assert has_property_argument(TO.parse("Pos(G)"))
    assert has_property_argument(TO.parse("Pos(λx. G(x))"))


def test_shadowing_stops_the_arity_scan_at_the_inner_binder():
    """The inner ∀P is a different P; the outer one is unapplied here."""
    node = TO.parse("∀P (Pos(P) ∧ ∀P (P(x, y) → P(x, y)))")
    assert _bound(node) == [("P", 1), ("P", 2)]


# --- the parse_any ladder ---------------------------------------------------

@pytest.mark.parametrize("text, dialect", [
    ("∀x P(x)", "fol"),
    ("□∀x P(x)", "modal"),
    ("∀P P(x)", "second_order"),
    ("Pos(G)", "third_order"),
    ("Ess(G, a)", "third_order"),
])
def test_parse_any_reaches_third_order_only_when_nothing_narrower_does(text, dialect):
    """The ladder is narrowest-first, and classical third order sits at the end.

    It is served by the same LALR table as `second_order`, so the only inputs it
    newly accepts are the ones with a predicate really standing in an argument
    slot — nothing previously detected as `fol`/`modal`/`second_order` moves.
    """
    from unicode_fol_kit.api import parse_any
    result = parse_any(text)
    assert result.ok and result.dialect == dialect


def test_the_modal_third_order_mode_is_deliberately_off_the_ladder():
    """Its Earley table reaches readings that would swallow malformed input.

    ``modal`` needs Earley, and ``third_order_modal`` inherits it; with a
    second-order binder also available, ``∀ P(x)`` parses there as a quantifier
    over the propositional atom ``x`` rather than failing as the malformed
    quantifier every other dialect reports. The repair and error-routing
    machinery depends on those dialects agreeing, so the mode is reached
    explicitly instead of by detection.
    """
    from unicode_fol_kit.api import parse_any, _UNICODE_MODES

    assert "third_order" in dict(_UNICODE_MODES)
    assert "third_order_modal" not in dict(_UNICODE_MODES)
    assert TOM.parse("∀ P(x)") is not None          # the mode really does accept it
    assert parse_any("∀ P(x)").ok is False          # and parse_any still refuses it
    assert parse_any("∀P (Pos(P) → □Pos(P))").ok is False


# --- spans ------------------------------------------------------------------

def test_parse_with_spans_agrees_with_parse_in_the_third_order_modes():
    for parser, text in ((TO, "Pos(λx. ¬G(x)) ∧ Ess(G, a)"),
                         (TOM, "∀P (Pos(P) → □Pos(P))")):
        assert parser.parse_with_spans(text).formula == parser.parse(text)
