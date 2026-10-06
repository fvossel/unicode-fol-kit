# -*- coding: utf-8 -*-
"""The typed arithmetic writer writes a numeral with its own digits and an operator a prover reads.

What is derived by hand:

* An integer is written with its digits, under both sorts, and never through a ``float`` (53 bits): the
  reals ``9007199254740993`` and ``9007199254740992`` differ by one, so ``9007199254740993 = 9007199254740992``
  is not valid (a structure with P = {2**53} refutes ``P(2**53) ⊢ P(2**53 + 1)``), while ``P(10**400) ⊢
  P(10**400)`` is valid and must be written, not stop with an ``OverflowError``.
* ``/`` over ``$int`` is the integer division ``$quotient_e`` (TPTP's ``$quotient`` is for ``$rat`` and
  ``$real``): the quotient ``q`` with ``a = b*q + r`` and ``0 <= r < |b|``, which is what Z3's ``/`` on integers
  is: ``-7 = 2*(-4) + 1``, ``7 = (-2)*(-3) + 1``, ``-7 = (-2)*4 + 1`` and ``7 = 2*3 + 1`` give ``-7 / 2 = -4``,
  ``7 / -2 = -3``, ``-7 / -2 = 4`` and ``7 / 2 = 3``; ``-7 / 2 = -3`` would leave the remainder ``-1``.
* A one-argument ``-`` (the node the Prover9 and SMT-LIB readers build for ``-t`` and ``(- t)``) is the
  negation, ``$uminus`` in the typed text and ``0 - t`` for Z3: ``-x + x = 0`` holds for every ``x``,
  ``-x = x`` fails at ``x = 1`` (``-1`` is not ``1``), and ``-(-x) = x`` holds. Every other operator is
  binary: ``$sum(X)`` and its like are ill-typed, the kit's other arithmetic route reads such a node as an
  uninterpreted function, and the writer refuses it by name.
* E 3.5.1 reads the typed text and then types ``$sum``, ``$difference``, ``$product`` and ``$quotient`` as
  functions into the individuals (a type error on every term that uses one), reads a ``$real`` literal only
  approximately (``0.1 = 0.1000001`` is a theorem for it, and these are two different reals) and does not
  evaluate a comparison. So the E route refuses an arithmetic function symbol, and a numeral under
  ``sort='real'``, by name, and asks E the rest.
"""

import re
import shutil
import subprocess

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import eprover_backend as _eb
from unicode_fol_kit.atp._tff_problem import (
    _render_number, formula_to_tff_arith, generate_tff_arith_problem,
)
from unicode_fol_kit.atp.eprover_backend import (
    EProverBackend, ZipperpositionBackend, check_entailment_eprover_detailed, eprover_available,
)
from unicode_fol_kit.atp.protocol import get_backend
from unicode_fol_kit.atp.vampire_entailment import check_entailment_vampire_detailed
from unicode_fol_kit.atp.z3_arith import is_valid_arith
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Implies, Not, Number, Or, Quantifier, Variable,
)

X = Variable("x")
TWO_53 = 2 ** 53


def Eq(left, right):
    return Atom("=", [left, right])


def P(*args):
    return Atom("P", list(args))


def forall(body, var=X):
    return Quantifier("∀", var, body)


def goal_text(formula, sort):
    text, _ = generate_tff_arith_problem([], formula, sort=sort)
    return text


# ---------------------------------------------------------------------------------------------
# The writer: a numeral is written with its own digits
# ---------------------------------------------------------------------------------------------

def test_two_integers_a_double_cannot_tell_apart_are_two_literals_under_real():
    text = goal_text(Eq(Number(TWO_53 + 1), Number(TWO_53)), "real")
    assert text == "tff(goal, conjecture, (9007199254740993.0 = 9007199254740992.0) ).\n"


def test_two_integers_a_double_cannot_tell_apart_are_two_literals_under_int():
    text = goal_text(Eq(Number(TWO_53 + 1), Number(TWO_53)), "int")
    assert text == "tff(goal, conjecture, (9007199254740993 = 9007199254740992) ).\n"


@pytest.mark.parametrize("sort, suffix", [("int", ""), ("real", ".0")])
def test_an_integer_of_400_digits_is_written_with_all_its_digits(sort, suffix):
    digits = "1" + "0" * 400
    text = goal_text(P(Number(10 ** 400)), sort)
    assert f"p({digits}{suffix})" in text and "e+" not in text and "inf" not in text


@pytest.mark.parametrize("sort, expected", [("int", "-9007199254740993"), ("real", "-9007199254740993.0")])
def test_a_negative_integer_keeps_its_digits_and_sign(sort, expected):
    assert f"p({expected})" in goal_text(P(Number(-(TWO_53 + 1))), sort)


def test_a_fractional_numeral_is_the_shortest_text_that_reads_back_as_it():
    assert "p(0.5)" in goal_text(P(Number(0.5)), "real")
    assert "p(0.30000000000000004)" in goal_text(P(Number(0.1 + 0.2)), "real")


def test_a_float_needing_an_exponent_is_refused_by_name():
    with pytest.raises(NotImplementedError, match="exponent"):
        goal_text(P(Number(1e-7)), "real")


@pytest.mark.parametrize("sort", ["int", "real"])
def test_a_bool_is_no_numeral_and_is_refused_not_written_as_a_word(sort):
    with pytest.raises(NotImplementedError, match="bool"):
        goal_text(P(Number(True)), sort)


@pytest.mark.parametrize("sort", ["int", "real"])
@pytest.mark.parametrize("value", [float("inf"), float("-inf"), float("nan")])
def test_a_non_finite_float_is_refused_by_name_and_is_never_written_as_the_word_inf(sort, value):
    # the entry points refuse it first, with the kit's own message; the literal writer refuses it too
    with pytest.raises((NotImplementedError, ValueError), match="finite"):
        goal_text(P(Number(value)), sort)
    with pytest.raises(NotImplementedError, match="finite"):
        _render_number(value, sort)


# ---------------------------------------------------------------------------------------------
# The writer: an operator a prover reads
# ---------------------------------------------------------------------------------------------

def test_a_division_over_int_is_the_integer_division_and_over_real_the_quotient():
    f = forall(Eq(Function("/", [X, Number(1)]), X))
    assert goal_text(f, "int") == "tff(goal, conjecture, (![X: $int]: ($quotient_e(X,1) = X)) ).\n"
    assert goal_text(f, "real") == "tff(goal, conjecture, (![X: $real]: ($quotient(X,1.0) = X)) ).\n"


def test_the_other_operators_are_the_same_words_over_both_sorts():
    for name, word in (("+", "$sum"), ("-", "$difference"), ("*", "$product")):
        f = forall(Eq(Function(name, [X, X]), X))
        for sort in ("int", "real"):
            assert f"({word}(X,X) = X)" in goal_text(f, sort)


@pytest.mark.parametrize("sort, zero", [("int", "0"), ("real", "0.0")])
def test_a_one_argument_minus_is_the_negation_on_both_arithmetic_routes(sort, zero):
    # ∀x (-x + x = 0): -x is 0 - x, and (0 - x) + x = 0 for every x
    cancels = forall(Eq(Function("+", [Function("-", [X]), X]), Number(0)))
    assert f"($sum($uminus(X),X) = {zero})" in goal_text(cancels, sort)
    assert formula_to_tff_arith(cancels, sort=sort) == f"(![X: ${sort}]: ($sum($uminus(X),X) = {zero}))"
    assert is_valid_arith(cancels, sort=sort) is True
    # ∀x (-x = x) fails at x = 1: -1 is not 1
    assert is_valid_arith(forall(Eq(Function("-", [X]), X)), sort=sort) is False
    # ∀x (-(-x) = x): 0 - (0 - x) = x
    assert is_valid_arith(forall(Eq(Function("-", [Function("-", [X])]), X)), sort=sort) is True


@pytest.mark.parametrize("name, args, count", [
    ("+", [X, X, X], 3), ("/", [X], 1), ("-", [X, X, X], 3), ("*", [X], 1),
])
def test_an_operator_at_a_number_of_arguments_other_than_two_is_refused_by_name(name, args, count):
    f = forall(Eq(Function(name, args), X))
    with pytest.raises(NotImplementedError, match=rf"'{re.escape(name)}' is applied to {count} argument"):
        goal_text(f, "real")


@pytest.mark.parametrize("predicate, args", [("<", 1), ("≥", 3), ("=", 1), ("≠", 3)])
def test_a_comparison_at_a_number_of_arguments_other_than_two_is_refused_by_name(predicate, args):
    f = forall(Atom(predicate, [X] * args))
    with pytest.raises(NotImplementedError, match=rf"'{re.escape(predicate)}' is applied to {args} argument"):
        goal_text(f, "int")


# ---------------------------------------------------------------------------------------------
# The E route refuses by name what E 3.5.1 cannot read or reads wrongly (no E needed)
# ---------------------------------------------------------------------------------------------

@pytest.fixture
def fake_e(monkeypatch):
    """E is found and 'runs': it records the problem it is given and answers Theorem."""
    problems = []

    def fake_run(problem, command, args, use_wsl, timeout_s):
        problems.append(problem)
        return "# SZS status Theorem for problem\n", False

    monkeypatch.setattr(_eb, "_discover", lambda name, env_var: ("eprover", False))
    monkeypatch.setattr(_eb, "_binary_version", lambda *a, **k: None)
    monkeypatch.setattr(_eb, "_run_tptp_prover", fake_run)
    return problems


@pytest.mark.parametrize("sort", ["int", "real"])
@pytest.mark.parametrize("operator", ["+", "-", "*", "/"])
def test_e_is_not_run_on_an_arithmetic_function_and_the_verdict_says_so(fake_e, sort, operator):
    goal = forall(P(Function(operator, [X, X])))
    verdict = EProverBackend().decide(goal, timeout=5000, sort=sort)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported"), verdict
    assert f"'{operator}'" in verdict.detail and "E 3.5.1" in verdict.detail and "Type error" in verdict.detail
    assert fake_e == []


def test_a_function_deep_inside_a_premise_is_found_too(fake_e):
    premise = forall(Implies(P(X), Not(Or(P(X), And(P(X), Eq(X, Function("*", [X, Number(2)])))))))
    verdict = EProverBackend().decide(P(Constant("a")), [premise], timeout=5000, sort="int")
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported") and fake_e == []


@pytest.mark.parametrize("value", [0, 1, 0.5, 2 ** 60, -3])
def test_a_numeral_under_real_is_refused_because_e_reads_a_real_literal_approximately(fake_e, value):
    verdict = EProverBackend().decide(P(Number(value)), [P(Number(value))], timeout=5000, sort="real")
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported"), verdict
    assert "sort='real'" in verdict.detail and str(value) in verdict.detail and fake_e == []


def test_the_two_reals_e_calls_equal_are_not_handed_to_it(fake_e):
    # 0.1 and 0.1000001 are two reals, so the goal is not valid, and E 3.5.1 proves it (measured)
    verdict = EProverBackend().decide(Eq(Number(0.1), Number(0.1000001)), timeout=5000, sort="real")
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported") and fake_e == []


@pytest.mark.parametrize("value", [0, 1, TWO_53 + 1, -3, 10 ** 30])
def test_a_numeral_under_int_is_asked_because_e_reads_an_integer_literal_exactly(fake_e, value):
    verdict = EProverBackend().decide(P(Number(value)), [P(Number(value))], timeout=5000, sort="int")
    assert verdict.status == "proved", verdict
    assert len(fake_e) == 1 and "$int" in fake_e[0]


def test_a_comparison_without_a_numeral_or_function_is_asked_under_real(fake_e):
    goal = forall(Atom("≤", [X, X]))
    verdict = EProverBackend().decide(goal, timeout=5000, sort="real")
    assert verdict.status == "proved" and len(fake_e) == 1 and "$lesseq(X,X)" in fake_e[0]


def test_without_a_sort_an_operator_is_an_uninterpreted_symbol_and_is_asked(fake_e):
    goal = forall(P(Function("+", [X, X])))
    verdict = EProverBackend().decide(goal, timeout=5000)
    assert verdict.status == "proved" and len(fake_e) == 1


def test_zipperposition_is_not_refused_because_its_reading_is_not_measured(fake_e):
    goal = forall(P(Function("+", [X, X])))
    verdict = ZipperpositionBackend().decide(goal, timeout=5000, sort="int")
    assert verdict.status == "proved" and len(fake_e) == 1 and "$sum" in fake_e[0]


def test_the_detailed_function_refuses_before_it_looks_for_a_binary(monkeypatch):
    def not_called(*args, **kwargs):
        raise AssertionError("no binary is looked for and no process is started for a refused problem")

    monkeypatch.setattr(_eb, "_discover", not_called)
    monkeypatch.setattr(_eb, "_run_tptp_prover", not_called)
    with pytest.raises(NotImplementedError, match="E 3.5.1"):
        check_entailment_eprover_detailed([], forall(P(Function("-", [X, X]))), sort="int")
    with pytest.raises(NotImplementedError, match="sort='real'"):
        check_entailment_eprover_detailed([], P(Number(1)), sort="real")


# ---------------------------------------------------------------------------------------------
# Live: Vampire and E answer the text the writer writes
# ---------------------------------------------------------------------------------------------

def _wsl_vampire_ok() -> bool:
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"], capture_output=True, text=True,
                                timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 -- any failure means "not available"
        return False


_VAMPIRE_ON_PATH = shutil.which("vampire")
_HAVE_VAMPIRE = _VAMPIRE_ON_PATH is not None or _wsl_vampire_ok()
_NEEDS_VAMPIRE = pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable")
_NEEDS_E = pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")


def _vampire_kwargs():
    if _VAMPIRE_ON_PATH is not None:
        return {"vampire_path": _VAMPIRE_ON_PATH, "use_wsl": False}
    return {"vampire_path": "vampire", "use_wsl": True}


def _vampire(goal, premises=(), sort="real", timeout=8):
    return check_entailment_vampire_detailed(list(premises), goal, timeout=timeout, sort=sort,
                                             **_vampire_kwargs())["status"]


@_NEEDS_VAMPIRE
@pytest.mark.parametrize("sort", ["int", "real"])
def test_vampire_does_not_prove_that_two_neighbouring_integers_are_one(sort):
    # not valid: the reals 2**53 + 1 and 2**53 differ (and the z3 route says so)
    goal = Eq(Number(TWO_53 + 1), Number(TWO_53))
    assert is_valid_arith(goal, sort=sort) is False
    assert _vampire(goal, sort=sort, timeout=4) != "proved"


@_NEEDS_VAMPIRE
def test_vampire_does_not_carry_a_property_from_one_integer_to_its_neighbour():
    # P = {2**53} refutes P(2**53) ⊢ P(2**53 + 1)
    assert _vampire(P(Number(TWO_53 + 1)), [P(Number(TWO_53))], sort="real", timeout=4) != "proved"


@_NEEDS_VAMPIRE
@pytest.mark.parametrize("sort", ["int", "real"])
def test_vampire_proves_a_property_of_an_integer_of_400_digits(sort):
    big = Number(10 ** 400)
    assert _vampire(P(big), [P(big)], sort=sort) == "proved"


def _euclid(a, b):
    r = a % abs(b)
    return (a - r) // b


@_NEEDS_VAMPIRE
@pytest.mark.parametrize("a, b, q", [(-7, 2, -4), (7, -2, -3), (-7, -2, 4), (7, 2, 3), (1, 2, 0), (0, 5, 0)])
def test_vampire_proves_the_euclidean_quotient_over_int_and_it_is_what_z3_says(a, b, q):
    assert _euclid(a, b) == q          # the hand-derived value: a = b*q + r with 0 <= r < |b|
    goal = Eq(Function("/", [Number(a), Number(b)]), Number(q))
    assert is_valid_arith(goal, sort="int") is True
    assert _vampire(goal, sort="int") == "proved"


@_NEEDS_VAMPIRE
def test_vampire_does_not_prove_a_quotient_with_a_negative_remainder():
    goal = Eq(Function("/", [Number(-7), Number(2)]), Number(-3))      # -7 = 2*(-3) + (-1)
    assert is_valid_arith(goal, sort="int") is False
    assert _vampire(goal, sort="int", timeout=4) != "proved"


@_NEEDS_VAMPIRE
def test_vampire_proves_x_divided_by_one_is_x_over_int_and_over_real():
    f = forall(Eq(Function("/", [X, Number(1)]), X))
    assert is_valid_arith(f, sort="int") is True and is_valid_arith(f, sort="real") is True
    assert _vampire(f, sort="int") == "proved"
    assert _vampire(f, sort="real") == "proved"


@_NEEDS_VAMPIRE
@pytest.mark.parametrize("sort", ["int", "real"])
def test_vampire_reads_the_one_argument_minus_as_the_negation(sort):
    # ∀x (-x + x = 0) holds; ∀x (-x = x) fails at x = 1
    cancels = forall(Eq(Function("+", [Function("-", [X]), X]), Number(0)))
    verdict = get_backend("vampire").decide(cancels, [], timeout=8000, sort=sort, **_vampire_kwargs())
    assert verdict.status == "proved", verdict
    fixed_point = forall(Eq(Function("-", [X]), X))
    assert _vampire(fixed_point, sort=sort) != "proved"


@_NEEDS_VAMPIRE
def test_an_operator_at_three_arguments_is_unknown_unsupported_not_a_failure_of_the_prover():
    f = forall(Eq(Function("+", [X, X, X]), X))
    verdict = get_backend("vampire").decide(f, [], timeout=8000, sort="int", **_vampire_kwargs())
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported"), verdict
    assert "'+' is applied to 3 argument" in verdict.detail


@_NEEDS_E
def test_e_never_refutes_a_valid_comparison_and_never_proves_an_invalid_one():
    # ∀x ∀y (x < y ∨ y ≤ x) is valid (trichotomy); ∃x x < x is not
    valid = forall(forall(Or(Atom("<", [X, Variable("y")]), Atom("≤", [Variable("y"), X])), Variable("y")))
    invalid = Quantifier("∃", X, Atom("<", [X, X]))
    for sort in ("int", "real"):
        assert is_valid_arith(valid, sort=sort) is True and is_valid_arith(invalid, sort=sort) is False
        assert check_entailment_eprover_detailed([], valid, sort=sort, timeout=8)["status"] in ("proved", "unknown")
        assert check_entailment_eprover_detailed([], invalid, sort=sort, timeout=8)["status"] != "proved"


@_NEEDS_E
@pytest.mark.parametrize("sort", ["int", "real"])
@pytest.mark.parametrize("text", ["1 + 1 = 2", "∀x x + 0 = x", "2 * 3 = 6", "2 - 3 = -1", "∀x x / 1 = x"])
def test_through_api_prove_e_says_what_it_cannot_read_and_does_not_fail(text, sort):
    # every one of these is valid arithmetic; E 3.5.1 stops with a type error on the text, so the answer
    # is unknown with the reason named, never an infrastructure failure
    formula = api.parse_any(text).formula
    assert is_valid_arith(formula, sort=sort) is True
    verdict = api.prove(formula, [], backends=["eprover"], timeout=8000, sort=sort)
    assert verdict.status == "unknown", verdict
    assert "unsupported" in verdict.detail and "E 3.5.1" in verdict.detail


@_NEEDS_E
def test_e_proves_what_needs_no_arithmetic_over_an_integer_literal():
    result = check_entailment_eprover_detailed([P(Number(TWO_53 + 1))], P(Number(TWO_53 + 1)), sort="int",
                                               timeout=8)
    assert result["status"] == "proved"
    other = check_entailment_eprover_detailed([P(Number(TWO_53))], P(Number(TWO_53 + 1)), sort="int", timeout=8)
    assert other["status"] != "proved"
