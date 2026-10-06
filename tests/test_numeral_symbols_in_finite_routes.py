r"""A numeral is ONE constant per VALUE on the finite-structure routes, and is never merged with a
constant spelled like it.

A numeral (a :class:`Number`) is a constant symbol identified by its value on every route that was
not asked for arithmetic: ``Number(1) == Number(1.0)``, so ``1`` and ``1.0`` are one constant, named
``'1'`` in the one table of constants of a structure (a free-logic model, a Tarski structure); two
numerals of different value may denote the same element (``⊢ 1 ≠ 2`` is not valid); ``+ - * /`` are
uninterpreted function symbols and ``< > ≤ ≥`` uninterpreted predicates. ``Number(1)`` next to
``Constant('1')`` would be one entry of that table for two symbols, so the pair is refused by name.

Where a route has an arithmetic reading of its own, a comparison of a cardinality ``|{x : φ}|`` with
a number, that reading stays: the number is then the bound the count is compared with, no individual.
The clingo encoder reads a number only there; a numeral anywhere else (an individual, or a comparison
of numerals with no cardinality in it) is refused by name, because a count-style reading of
``1 = 2`` would make ``(∀x ∀y x = y) → 1 = 2`` (valid: one element) refutable.

The free-logic readings are derived by hand from negative free logic: a constant that is absent from the
model does not denote, an atom with a non-denoting term is false, so ``∀x P(x) ⊢ P(1)`` is NOT valid
(``1`` may not denote an existing object) and ``∀x P(x), E!(1) ⊢ P(1)`` is.
"""

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.clingo_backend import clingo_available
from unicode_fol_kit.fol.nodes import (
    And, Atom, Cardinality, Constant, Count, Function, Iff, Implies, Not, Number, Or, Quantifier,
    SortedConstant, Variable,
)
from unicode_fol_kit.semantics.asp_models import asp_find_model
from unicode_fol_kit.semantics.free_logic import (
    FreeModel, free_countermodel, free_entails, free_find_model, free_holds, free_is_valid, free_satisfies,
)
from unicode_fol_kit.semantics.modelfinder import (
    find_countermodel, find_model, is_size_exhaustive, is_valid_finite, search_model,
)
from unicode_fol_kit.semantics.tarski import Structure, models, satisfies

x, y = Variable("x"), Variable("y")


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


def _eq(left, right):
    return Atom("=", [left, right])


def _formula(text):
    result = api.parse_any(text)
    assert result.ok, text
    return result.formula


def _count_at_least(number):
    return Atom("≥", [Cardinality(x, P(x)), number])


# --------------------------------------------------------------------------- #
# The Tarski evaluator.
# --------------------------------------------------------------------------- #

_STRUCTURE = Structure(["a", "b"], constants={"1": "a", "2": "b"}, predicates={("P", 1): {("a",)}, ("Q", 1): {("b",)}})


def test_a_numeral_is_read_under_the_name_of_its_value():
    assert satisfies(And(P(Number(1)), P(Number(1.0))), _STRUCTURE)
    assert satisfies(Q(Number(2.0)), _STRUCTURE)
    assert not satisfies(P(Number(2)), _STRUCTURE)


@pytest.mark.parametrize("numeral", [Number(1), Number(1.0)])
def test_a_numeral_and_a_constant_named_like_its_value_are_refused_by_name(numeral):
    # One entry '1' of the constants would serve both symbols.
    for formula in (And(P(numeral), Q(Constant("1"))), And(Q(Constant("1")), P(numeral)),
                    Quantifier("∀", y, Implies(P(y), And(P(numeral), Q(Constant("1"))))),
                    Not(Or(P(numeral), P(SortedConstant("1", "S"))))):
        with pytest.raises(NotImplementedError, match="ONE entry"):
            satisfies(formula, _STRUCTURE)
        with pytest.raises(NotImplementedError, match="ONE entry"):
            models(formula, _STRUCTURE)


def test_the_refusal_names_the_two_symbols_and_what_to_do():
    with pytest.raises(NotImplementedError) as refused:
        satisfies(And(P(Number(1)), P(Constant("1"))), _STRUCTURE)
    message = str(refused.value)
    assert "the number 1 and the constant '1'" in message and "Rename the constant" in message


def test_a_formula_that_passed_does_not_excuse_another_formula_with_the_clash():
    ok = And(P(Number(1)), P(Constant("one")))
    clash = And(P(Number(1)), P(Constant("1")))
    structure = Structure(["a", "b"], constants={"1": "a", "one": "a"}, predicates={("P", 1): {("a",)}})
    for _ in range(3):
        assert satisfies(ok, structure)
        with pytest.raises(NotImplementedError):
            satisfies(clash, structure)
    # an equal formula built again is checked like any other
    with pytest.raises(NotImplementedError):
        satisfies(And(P(Number(1.0)), P(Constant("1"))), structure)


def test_the_bound_of_a_counting_quantifier_and_the_operand_of_a_cardinality_comparison_are_no_individuals():
    # The 1 of the counting quantifier and the 1 a cardinality is compared with are numbers the
    # evaluator reads as themselves; the constant '1' is an individual. They are two things.
    structure = Structure([0, 1], constants={"1": 0}, predicates={("P", 1): {(0,)}})
    assert satisfies(And(Count("ge", Number(1), x, P(x)), P(Constant("1"))), structure)
    assert satisfies(And(_count_at_least(Number(1)), P(Constant("1"))), structure)
    assert satisfies(And(Atom("=", [Number(1), Cardinality(x, P(x))]), P(Constant("1"))), structure)


def test_a_comparison_that_is_not_a_cardinality_comparison_reads_its_numerals_as_individuals():
    # R(|{x : P(x)}|, 1) is no comparison: its 1 is looked up like any numeral.
    formula = And(Atom("R", [Cardinality(x, P(x)), Number(1)]), P(Constant("1")))
    structure = Structure([0, 1], constants={"1": 0}, predicates={("P", 1): {(0,)}, ("R", 2): {(1, 0)}})
    with pytest.raises(NotImplementedError, match="ONE entry"):
        satisfies(formula, structure)


# --------------------------------------------------------------------------- #
# The model finder.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("numeral", [Number(1), Number(1.0)])
def test_the_model_finder_refuses_a_numeral_and_a_constant_named_like_its_value(numeral):
    pair = And(P(numeral), Q(Constant("1")))
    for call in (lambda: find_model([pair]), lambda: find_model([P(numeral), Q(Constant("1"))]),
                 lambda: find_countermodel([P(numeral)], Q(Constant("1"))),
                 lambda: find_countermodel([Q(Constant("1"))], P(numeral)),
                 lambda: search_model([pair]), lambda: is_valid_finite(Implies(P(numeral), Q(Constant("1")))),
                 lambda: is_size_exhaustive([pair], 2),
                 lambda: find_model([And(P(numeral), Q(SortedConstant("1", "S")))])):
        with pytest.raises(NotImplementedError, match="ONE entry"):
            call()


def test_the_model_finder_does_not_answer_a_refused_pair_through_the_prove_surface():
    verdict = api.prove(Q(Constant("1")), [P(Number(1))], backends=["modelfinder"], timeout=10000)
    assert verdict.status == "unknown" and "ONE entry" in (verdict.detail or "")


def test_the_model_finder_reads_the_numbers_of_a_count_as_no_constants():
    model = find_model([And(Count("ge", Number(1), x, P(x)), P(Constant("1")))])
    assert model is not None and satisfies(And(Count("ge", Number(1), x, P(x)), P(Constant("1"))), model)
    model = find_model([And(_count_at_least(Number(2)), Q(Constant("2")))])
    assert model is not None and len(model.domain) >= 2


def test_the_model_finder_still_finds_the_one_constant_of_a_value():
    # One numeral '1' and one numeral '2': a countermodel of 1 != 2 has them equal.
    model = find_countermodel([], Atom("≠", [Number(1), Number(2)]))
    assert model is not None and set(model.constants) == {"1", "2"} and model.constants["1"] == model.constants["2"]
    assert find_countermodel([P(Number(1))], P(Number(1.0))) is None


# --------------------------------------------------------------------------- #
# Free logic.
# --------------------------------------------------------------------------- #

def _model(constants, predicates=None, outer=(0, 1), existing=None):
    return FreeModel(outer=tuple(outer), existing=frozenset(outer if existing is None else existing),
                     constants=constants, predicates=predicates or {})


def test_a_free_logic_numeral_is_looked_up_under_the_name_of_its_value():
    model = _model({"1": 0}, {("P", 1): frozenset({(0,)})})
    assert free_satisfies(P(Number(1)), model) and free_satisfies(P(Number(1.0)), model)
    # The name '1.0' is not the name of a value: a table that holds it holds a constant nobody reads.
    assert not free_satisfies(P(Number(1.0)), _model({"1.0": 0}, {("P", 1): frozenset({(0,)})}))
    assert free_satisfies(_eq(Number(1), Number(1.0)), _model({"1": 1}))
    assert free_satisfies(Atom("≠", [Number(1), Number(2)]), _model({"1": 0, "2": 1}))
    assert not free_satisfies(Atom("≠", [Number(1), Number(2)]), _model({"1": 1, "2": 1}))


@pytest.mark.parametrize("policy", ["negative", "positive", "supervaluation"])
def test_a_free_logic_numeral_of_one_value_is_one_constant_under_every_policy(policy):
    # P(1) |- P(1.0): one constant; if it does not denote both atoms are false, if it does they agree.
    assert free_entails([P(Number(1))], P(Number(1.0)), policy=policy)
    assert free_entails([P(Number(1.0))], P(Number(1)), policy=policy)
    assert free_is_valid(Implies(P(Number(1)), P(Number(1.0))), policy=policy)
    assert free_countermodel(Implies(P(Number(1.0)), P(Number(1))), policy=policy) is None


def test_supervaluation_holds_a_non_denoting_numeral_to_one_precisified_value():
    # 1 and 1.0 do not denote. P(1) v ~P(1.0) is P(e) v ~P(e) for ONE gap atom: supertrue. With two
    # unrelated gap atoms a precisification could make both disjuncts false.
    model = _model({}, outer=(0,))
    formula = Or(P(Number(1)), Not(P(Number(1.0))))
    assert free_satisfies(formula, model, policy="supervaluation")
    assert free_satisfies(Or(P(Number(1)), Not(P(Number(2)))), model, policy="supervaluation") is False


def test_numerals_of_different_value_are_different_constants_in_free_logic():
    # not valid: 1 and 2 may denote one object, or one of them may not denote
    for premises, goal in (([], Atom("≠", [Number(1), Number(2)])), ([P(Number(1))], P(Number(2))),
                           ([P(Number(1)), P(Number(2))],
                            Quantifier("∃", x, Quantifier("∃", y, And(Atom("≠", [x, y]), And(P(x), P(y)))))),
                           ([P(Number(1))], P(Constant("one"))),
                           ([], Atom("<", [Number(1), Number(2)])),
                           ([], _eq(Function("+", [Number(1), Number(1)]), Number(2)))):
        assert not free_entails(premises, goal), (premises, goal)


def test_a_free_logic_numeral_is_an_instance_only_when_it_exists():
    # negative free logic: forall x P(x) does not say anything of an object that may not exist
    assert not free_entails([Quantifier("∀", x, P(x))], P(Number(1)))
    assert free_entails([Quantifier("∀", x, P(x)), Atom("E!", [Number(1)])], P(Number(1)))
    assert free_entails([Quantifier("∀", x, P(x)), Atom("E!", [Number(1)])], P(Number(1.0)))
    # a negative numeral must be writable and read: P(-1) holds of -1, which may not exist
    assert free_entails([P(Number(-1)), Atom("E!", [Number(-1)])], Quantifier("∃", x, P(x)))
    assert not free_entails([P(Number(-1))], Quantifier("∃", x, P(x)))


def test_self_identity_of_a_decimal_numeral_is_valid_only_under_positive_free_logic():
    reflexivity = _eq(Number(2.5), Number(2.5))
    assert free_is_valid(reflexivity, policy="positive")
    assert not free_is_valid(reflexivity, policy="negative")


def test_the_free_logic_search_holds_one_entry_per_value():
    model = free_find_model(And(P(Number(1)), P(Number(1.0))))
    assert model is not None and set(model.constants) == {"1"}
    model = free_countermodel(Atom("≠", [Number(1), Number(2)]), max_size=1)
    assert model is not None and set(model.constants) <= {"1", "2"}


@pytest.mark.parametrize("numeral", [Number(1), Number(1.0)])
def test_free_logic_refuses_a_numeral_and_a_constant_named_like_its_value(numeral):
    pair = And(P(numeral), Q(Constant("1")))
    model = _model({"1": 0})
    for call in (lambda: free_satisfies(pair, model), lambda: free_holds(pair, model),
                 lambda: free_satisfies(pair, model, policy="supervaluation"),
                 lambda: free_entails([P(numeral)], Q(Constant("1"))),
                 lambda: free_is_valid(Implies(P(numeral), Q(Constant("1")))),
                 lambda: free_find_model(pair), lambda: free_countermodel(pair)):
        with pytest.raises(NotImplementedError, match="ONE entry"):
            call()


# --------------------------------------------------------------------------- #
# The ASP model finder.
# --------------------------------------------------------------------------- #

needs_clingo_module = pytest.mark.skipif(not clingo_available(), reason="clingo is not installed")


@needs_clingo_module
@pytest.mark.parametrize("size", [1, 2, 3])
def test_asp_has_no_countermodel_of_one_constant_per_value(size):
    # P(1), not P(1.0): a contradiction when 1 and 1.0 are one constant (no structure of any size)
    assert asp_find_model([P(Number(1)), Not(P(Number(1.0)))], size=size) is None
    assert asp_find_model([P(Number(1.0)), Not(P(Number(1)))], size=size) is None
    structure = asp_find_model([P(Number(1.0))], size=size)
    assert structure is not None and set(structure.constants) == {"1"}


@needs_clingo_module
def test_asp_finds_the_one_element_structure_where_two_numerals_denote_one_element():
    structure = asp_find_model([_eq(Number(1), Number(2))], size=1)
    assert structure is not None and structure.constants == {"1": 0, "2": 0}
    assert asp_find_model([Atom("≠", [Number(1), Number(2)])], size=1) is None
    assert asp_find_model([Atom("≠", [Number(1), Number(2)])], size=2) is not None


@needs_clingo_module
@pytest.mark.parametrize("numeral", [Number(1), Number(1.0)])
def test_asp_refuses_a_numeral_and_a_constant_named_like_its_value(numeral):
    with pytest.raises(NotImplementedError, match="ONE entry"):
        asp_find_model([And(P(numeral), Q(Constant("1")))], size=2)
    with pytest.raises(NotImplementedError, match="ONE entry"):
        asp_find_model([P(numeral), Q(Constant("1"))], size=2)


@needs_clingo_module
def test_asp_reads_the_bound_of_a_count_as_no_constant():
    formula = And(Count("ge", Number(1), x, P(x)), P(Constant("1")))
    structure = asp_find_model([formula], size=2)
    assert structure is not None and "1" in structure.constants     # the constant; the bound 1 is no entry
    assert satisfies(formula, structure)


# --------------------------------------------------------------------------- #
# The clingo backend: a count keeps its arithmetic reading, a numeral is refused by name elsewhere.
# --------------------------------------------------------------------------- #

_NO_CLINGO = "clingo is not installed"
needs_clingo = pytest.mark.skipif(not clingo_available(), reason=_NO_CLINGO)

# premises, goal, valid under the definition, why
_CLINGO_NUMERAL_PROBLEMS = [
    (["∀x P(x)"], "P(1)", True, "an instance"),
    (["P(1)"], "P(1.0)", True, "one constant"),
    ([], "1 ≠ 2", False, "one element"),
    ([], "1 < 2", False, "< is empty"),
    ([], "1 + 1 = 2", False, "+ is constantly 0 on {0, 1}"),
    (["P(1)", "P(2)"], "∃x ∃y (x ≠ y ∧ P(x) ∧ P(y))", False, "one element"),
    (["P(1)"], "P(one)", False, "two elements, P = {0}"),
    (["∀x ∀y x + y = y + x"], "1 + 2 = 2 + 1", True, "an instance"),
    (["∀x (x < 2 → Q(x))", "1 < 2"], "Q(1)", True, "an instance and modus ponens"),
    ([], "2.5 = 2.5", True, "reflexivity"),
    (["P(-1)"], "∃x P(x)", True, "an instance of the existential"),
    # valid because ONE element makes 1 and 2 denote one thing; an arithmetic reading refutes them
    ([], "(∀x ∀y x = y) → (1 < 2 ↔ 2 < 1)", True, "one element: 1 and 2 denote the same thing"),
    ([], "(∀x ∀y x = y) → 1 = 2", True, "one element"),
    (["∀x ∀y x = y"], "1 = 2", True, "one element"),
]


@needs_clingo
@pytest.mark.parametrize("premises, goal, valid, why", _CLINGO_NUMERAL_PROBLEMS,
                         ids=[goal for _, goal, _, _ in _CLINGO_NUMERAL_PROBLEMS])
def test_clingo_refuses_a_numeral_by_name_and_never_answers_the_opposite(premises, goal, valid, why):
    verdict = api.prove(_formula(goal), [_formula(p) for p in premises], backends=["clingo"], timeout=20000,
                        max_size=3)
    assert verdict.status != "proved"
    if valid:
        assert verdict.status != "refuted", (goal, why, verdict)
    # Each of them has a numeral outside a count (or a symbol the encoder does not declare):
    # refused by name, with the reason `unsupported` from the clingo backend.
    assert verdict.status == "unknown" and "clingo:unknown/unsupported" in (verdict.detail or ""), (goal, verdict)


@needs_clingo
@pytest.mark.parametrize("bound", [Number(2), Number(2.0)])
def test_clingo_still_refutes_a_cardinality_compared_with_a_bound(bound):
    # |{x : P(x)}| >= 2 is not valid: P empty. A whole-number float is the same bound.
    verdict = api.prove(_count_at_least(bound), [], backends=["clingo"], timeout=20000, max_size=3)
    assert verdict.status == "refuted", verdict


@needs_clingo
@pytest.mark.parametrize("bound", [Number(0), Number(0.0)])
def test_clingo_finds_no_countermodel_of_a_count_that_is_at_least_zero(bound):
    verdict = api.prove(_count_at_least(bound), [], backends=["clingo"], timeout=20000, max_size=3)
    assert verdict.status == "unknown" and "clingo:unknown/bound_hit" in (verdict.detail or ""), verdict


@needs_clingo
def test_clingo_reads_a_count_against_a_constant_named_like_its_bound_as_two_things():
    goal = And(_count_at_least(Number(2)), Q(Constant("2")))
    verdict = api.prove(Not(goal), [], backends=["clingo"], timeout=20000, max_size=3)
    assert verdict.status == "refuted"      # a model: P holds of two elements, Q of the constant 2
