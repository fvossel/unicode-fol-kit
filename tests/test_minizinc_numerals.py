r"""MiniZinc reads a numeral only as the bound a cardinality is compared with.

A numeral (a :class:`~unicode_logic_kit.fol.nodes.Number`) is a constant identified by its value on
every route that was not asked for arithmetic: two numerals of different value may denote the same
element, so ``1 = 2`` is not valid, and ``(∀x ∀y x = y) → 1 = 2`` is (one element, so ``1`` and
``2`` denote the same thing). MiniZinc's domain individuals are the integers ``0 … size-1``, and the
bare literal ``k`` would be the element number ``k``: that reading refuted the valid problems above.
The counting fragment keeps its own reading, a number is the bound of ``|{x : P(x)}| ≥ 2``.

So a numeral is refused by name everywhere else (a term of a predicate, of a function, of ``=``, a
comparison of numerals with no cardinality in it), and a cardinality set against a plain individual
is refused too. A refusal reaches ``api.prove`` as ``unknown`` / ``unsupported``.

Every verdict below is derived by hand:

* ``P(1) ⊢ P(1.0)``, ``(∀x ∀y x = y) → 1 = 2``, ``∀x ∀y x = y ⊢ 1 = 2``: valid. A countermodel
  would need two elements, or ``P(1)`` true and ``P(1.0)`` false, which are one atom.
* ``⊢ |{x : P(x)}| ≥ 2`` is not valid: ``P`` empty has no two elements. ``⊢ |{x : P(x)}| ≥ 0`` is
  valid (a count is never negative), so there is no countermodel at any size.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import minizinc_backend as mb
from unicode_logic_kit.atp.finite_domain import FiniteDomainProblem
from unicode_logic_kit.atp.minizinc_backend import minizinc_available, to_minizinc
from unicode_logic_kit.fol.nodes import (
    And, Atom, Cardinality, Constant, Count, Function, Implies, Not, Number, Quantifier, Variable,
)

x, y = Variable("x"), Variable("y")


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


def _count(variable=x, predicate="P"):
    return Cardinality(variable, Atom(predicate, [variable]))


def _render(*sentences, size=3):
    return to_minizinc(FiniteDomainProblem(tuple(sentences), size))


def _formula(text):
    result = api.parse_any(text)
    assert result.ok, text
    return result.formula


# --------------------------------------------------------------------------- #
# The renderer (no MiniZinc binary needed).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("sentence", [
    P(Number(1)),
    P(Function("f", [Number(1)])),
    Quantifier("∃", x, Atom("=", [x, Number(2)])),
    Quantifier("∃", x, Atom("=", [Number(2), x])),
    Atom("=", [Number(1), Number(2)]),
    Atom("≠", [Number(1), Number(2)]),
    Atom("<", [Number(1), Number(2)]),
    Atom("≥", [Number(1), Number(2)]),
    Atom("=", [Number(1), Constant("c")]),
    Atom("=", [Number(2.5), Number(2.5)]),
    Atom("=", [Function("+", [Number(1), Number(1)]), Number(2)]),
], ids=["predicate argument", "function argument", "variable = numeral", "numeral = variable",
        "1 = 2", "1 ≠ 2", "1 < 2", "1 ≥ 2", "numeral = constant", "2.5 = 2.5", "1 + 1 = 2"])
def test_a_numeral_that_is_no_bound_of_a_count_is_refused_by_name(sentence):
    with pytest.raises(NotImplementedError, match="numeral"):
        _render(sentence)


def test_the_refusal_says_what_a_numeral_is_and_what_to_do():
    with pytest.raises(NotImplementedError) as refused:
        _render(Atom("=", [Number(1), Number(2)]))
    message = str(refused.value)
    assert "constant identified by its value" in message and "(∀x ∀y x = y) → 1 = 2" in message
    assert "z3" in message and "model finder" in message
    with pytest.raises(NotImplementedError) as refused:
        _render(P(Number(1)))
    assert "used as an individual" in str(refused.value) and "constant" in str(refused.value)


def test_a_numeral_inside_a_cardinality_comparison_but_not_its_bound_is_refused():
    # |{x : P(x)}| = f(1): a count against an individual term, which holds a numeral
    with pytest.raises(NotImplementedError, match="cardinality against a plain"):
        _render(Atom("=", [_count(), Function("f", [Number(1)])]))
    # P(1) inside the counted formula is an individual position
    with pytest.raises(NotImplementedError, match="used as an individual"):
        _render(Atom("≥", [Cardinality(x, And(P(x), Q(Number(1)))), Number(2)]))


def test_a_cardinality_set_against_a_plain_individual_is_refused():
    with pytest.raises(NotImplementedError, match="cardinality against a plain"):
        _render(Atom("=", [_count(), Constant("c")]))
    with pytest.raises(NotImplementedError, match="cardinality against a plain"):
        _render(Atom("<", [Constant("c"), _count()]))


@pytest.mark.parametrize("op, mzn", [("=", "="), ("≠", "!="), ("<", "<"), (">", ">"), ("≤", "<="), ("≥", ">=")])
def test_a_number_compared_with_a_cardinality_is_the_bound_of_the_count(op, mzn):
    count = "sum(v_x in DOM)(bool2int(p_P[v_x]))"
    assert f"constraint ({count} {mzn} 2);" in _render(Atom(op, [_count(), Number(2)]))
    assert f"constraint (2 {mzn} {count});" in _render(Atom(op, [Number(2), _count()]))


def test_a_float_with_a_whole_value_is_the_same_bound():
    # Number(2.0) IS Number(2): the one numeral, so the one text
    assert _render(Atom("≥", [_count(), Number(2.0)])) == _render(Atom("≥", [_count(), Number(2)]))
    assert "(sum(v_x in DOM)(bool2int(p_P[v_x])) >= 0);" in _render(Atom("≥", [_count(), Number(0.0)]))


def test_a_count_compared_with_a_count_and_a_counting_quantifier_are_unchanged():
    text = _render(Atom(">", [_count(x, "Q"), _count(y, "R")]), Count("ge", Number(2), x, P(x)))
    assert "constraint (sum(v_x in DOM)(bool2int(p_Q[v_x])) > sum(v_y in DOM)(bool2int(p_R[v_y])));" in text
    assert "constraint (sum(v_x in DOM)(bool2int(p_P[v_x])) >= 2);" in text


def test_a_fraction_is_no_bound_of_a_count():
    for operands in ([_count(), Number(1.5)], [Number(2.5), _count()]):
        with pytest.raises(NotImplementedError, match="not an integer"):
            _render(Atom("=", operands))


def test_a_bool_is_no_bound_of_a_count():
    with pytest.raises(NotImplementedError, match="not an integer"):
        _render(Atom("=", [_count(), Number(True)]))


# --------------------------------------------------------------------------- #
# Through the prove surface, live (these need a MiniZinc binary: $UFK_MINIZINC or PATH).
# --------------------------------------------------------------------------- #

needs_minizinc = pytest.mark.skipif(not minizinc_available(), reason="MiniZinc is not installed")

# premises, goal, valid under the definition, why
_NUMERAL_PROBLEMS = [
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
    # valid because ONE element makes 1 and 2 denote one thing; the index reading refuted them
    ([], "(∀x ∀y x = y) → (1 < 2 ↔ 2 < 1)", True, "one element: 1 and 2 denote the same thing"),
    ([], "(∀x ∀y x = y) → 1 = 2", True, "one element"),
    (["∀x ∀y x = y"], "1 = 2", True, "one element"),
]


@needs_minizinc
@pytest.mark.parametrize("premises, goal, valid, why", _NUMERAL_PROBLEMS,
                         ids=[goal for _, goal, _, _ in _NUMERAL_PROBLEMS])
def test_minizinc_refuses_a_numeral_by_name_and_never_answers_the_opposite(premises, goal, valid, why):
    verdict = api.prove(_formula(goal), [_formula(p) for p in premises], backends=["minizinc"], timeout=30000,
                        max_size=3)
    assert verdict.status != "proved"
    if valid:
        assert verdict.status != "refuted", (goal, why, verdict)
    # Each of them has a numeral outside a count: refused by name, `unsupported` from the backend.
    assert verdict.status == "unknown" and "minizinc:unknown/unsupported" in (verdict.detail or ""), (goal, verdict)


@needs_minizinc
@pytest.mark.parametrize("bound", [Number(2), Number(2.0)])
def test_minizinc_still_refutes_a_cardinality_compared_with_a_bound(bound):
    # |{x : P(x)}| >= 2 is not valid: P empty. A whole-number float is the same bound.
    verdict = api.prove(Atom("≥", [_count(), bound]), [], backends=["minizinc"], timeout=30000, max_size=3)
    assert verdict.status == "refuted", verdict


@needs_minizinc
def test_minizinc_still_refutes_with_the_bound_on_the_left_and_with_a_counting_quantifier():
    assert api.prove(Atom("≤", [Number(2), _count()]), [], backends=["minizinc"], timeout=30000,
                     max_size=3).status == "refuted"
    assert api.prove(Count("ge", Number(2), x, P(x)), [], backends=["minizinc"], timeout=30000,
                     max_size=3).status == "refuted"


@needs_minizinc
def test_minizinc_finds_no_countermodel_of_a_count_that_is_at_least_zero():
    verdict = api.prove(Atom("≥", [_count(), Number(0)]), [], backends=["minizinc"], timeout=30000, max_size=3)
    assert verdict.status == "unknown" and "minizinc:unknown/bound_hit" in (verdict.detail or ""), verdict


@needs_minizinc
def test_minizinc_reads_a_count_against_a_constant_named_like_its_bound_as_two_things():
    # |{x : P(x)}| >= 2 and Q(2) are two facts: a model gives P two elements and the constant `2` its own atom.
    goal = And(Atom("≥", [_count(), Number(2)]), Q(Constant("2")))
    verdict = api.prove(Not(goal), [], backends=["minizinc"], timeout=30000, max_size=3)
    assert verdict.status == "refuted", verdict
