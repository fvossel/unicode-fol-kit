r"""A numeral has ONE spelling per value: ``Number(1.0)`` IS ``Number(1)``.

A :class:`~unicode_logic_kit.fol.nodes.Number` is a constant identified by its value, and
``Number(1) == Number(1.0)`` (equal, equal hash). The node stores a float with a whole value as
the integer it equals, so that equal numerals are the same node, with the same ``repr``, the same
``to_dict`` and the same printed text in every syntax. A route that keys an atom by its printed
text (the truth table, the Kripke enumerator, the intuitionistic and counterfactual searches) then
reads ``P(1)`` and ``P(1.0)`` as the ONE atom they are.

Every expectation is derived by hand. ``P(1) → P(1.0)`` is ``A → A`` once the two atoms are one, a
tautology of every logic below, and ``□P(1) ⊢ □P(1.0)`` is ``□A ⊢ □A``. As controls,
``P(1) → P(2)`` is ``A → B`` (A true, B false refutes it: two different numerals are two atoms)
and ``P(1) → P(2.5)`` likewise.
"""

import json

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp._tff_problem import generate_tff_arith_problem
from unicode_logic_kit.atp.kripke_enum import modal_enum_search
from unicode_logic_kit.atp.lj import int_prove
from unicode_logic_kit.atp.z3_arith import is_valid_arith, to_z3_arith
from unicode_logic_kit.fol._fol_nodes import numeral_key
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Count, Function, Iff, Implies, Node, Not, Number, Or, Variable,
)
from unicode_logic_kit.fol.prolog_export import formula_to_prolog_clause
from unicode_logic_kit.fol.prolog_input import parse_prolog_clause
from unicode_logic_kit.fol.prover9_input import parse_prover9
from unicode_logic_kit.fol.tptp_input import parse_tptp
from unicode_logic_kit.semantics import truthtable
from unicode_logic_kit.semantics.conditional import cf_valid
from unicode_logic_kit.semantics.intuitionistic import int_valid
from unicode_logic_kit.semantics.kripke import satisfies_modal

x = Variable("x")


def P(*args):
    return Atom("P", list(args))


# --------------------------------------------------------------------------- #
# The node.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("float_value, value", [
    (1.0, 1), (100.0, 100), (-0.0, 0), (0.0, 0), (-3.0, -3), (1e16, 10 ** 16), (1e22, 10 ** 22),
    # the double nearest 10**23 is 2980232238769531 * 2**25 = 10**23 - 8388608, and the node holds that integer
    (1e23, 99999999999999991611392), (2.0 ** 70, 2 ** 70),
])
def test_a_float_with_a_whole_value_is_stored_as_the_integer_it_equals(float_value, value):
    node = Number(float_value)
    assert type(node.value) is int and node.value == value == float_value
    assert node == Number(value) and hash(node) == hash(Number(value))
    assert repr(node) == f"Number(value={value})" == repr(Number(value))
    assert node.to_dict() == {"_type": "Number", "value": value}


@pytest.mark.parametrize("value", [2.5, -2.5, 0.1, 1e-07, 5e-324, 1.5])
def test_a_value_that_is_no_whole_number_stays_a_float(value):
    node = Number(value)
    assert type(node.value) is float and node.value == value


@pytest.mark.parametrize("value", [float("inf"), float("-inf")])
def test_a_non_finite_float_is_kept_and_refused_by_name_when_it_is_written(value):
    node = Number(value)
    assert type(node.value) is float
    with pytest.raises(ValueError, match="has no literal"):
        P(node).to_unicode_str()


def test_a_bool_is_not_read_as_a_number():
    # Number(True) is kept as it is (the routes that need an integer refuse a bool by name).
    assert Number(True).value is True


_GRID = [0, 0.0, -0.0, 1, 1.0, -1, -1.0, 2.5, 2.50, -2.5, 0.1, 1e-07, 1e16, 10 ** 16, 1e22, 10 ** 22,
         1e23, 10 ** 23, 2 ** 53, float(2 ** 53), 2 ** 53 + 1, 2.0 ** 70, 2 ** 70]


def test_two_numerals_are_the_same_node_exactly_when_their_values_are_equal():
    # Python's == between an int and a float is exact (10**23 != 1e23, which is 10**23 - 8388608).
    for a in _GRID:
        for b in _GRID:
            first, second = Number(a), Number(b)
            same = a == b
            assert (first == second) is same, (a, b)
            assert (repr(first) == repr(second)) is same, (a, b)
            assert (P(first).to_unicode_str() == P(second).to_unicode_str()) is same, (a, b)
            assert (numeral_key(first.value) == numeral_key(second.value)) is same, (a, b)
            if same:
                assert hash(first) == hash(second) and first.to_dict() == second.to_dict()


def test_equal_numerals_are_one_element_of_a_set_and_one_key_of_a_dict():
    assert len({Number(1), Number(1.0), Number(1.00)}) == 1
    assert len({Number(0), Number(-0.0), Number(0.0)}) == 1
    assert len({Number(2.5), Number(2.50)}) == 1
    assert len({Number(1), Number(2), Number(2.0)}) == 2
    assert {Number(1.0): "one"}[Number(1)] == "one"


@pytest.mark.parametrize("value", _GRID)
def test_a_numeral_survives_a_dict_and_a_json_round_trip_as_the_same_node(value):
    node = Number(value)
    assert Node.from_dict(node.to_dict()) == node
    back = Node.from_dict(json.loads(json.dumps(node.to_dict())))
    assert back == node and repr(back) == repr(node) and type(back.value) is type(node.value)


def test_a_dict_that_holds_a_whole_float_is_read_as_the_integer():
    # a JSON document written by another tool may say 3.0
    node = Node.from_dict(json.loads('{"_type": "Number", "value": 3.0}'))
    assert node == Number(3) and type(node.value) is int


def test_a_count_with_a_whole_float_bound_is_the_count_of_that_integer():
    # Count refuses a bound that is not a non-negative integer. 2.0 IS the integer 2, so it is one.
    bound = Count("ge", Number(2.0), x, P(x))
    assert bound == Count("ge", Number(2), x, P(x)) and bound.to_unicode_str() == "∃≥2 x P(x)"
    with pytest.raises(ValueError, match="non-negative integer"):
        Count("ge", Number(2.5), x, P(x))
    with pytest.raises(ValueError, match="non-negative integer"):
        Count("ge", Number(-2.0), x, P(x))


# --------------------------------------------------------------------------- #
# The text.
# --------------------------------------------------------------------------- #

def test_every_text_renderer_writes_the_one_spelling_of_a_whole_value():
    for whole, text in ((1.0, "1"), (100.0, "100"), (-0.0, "0"), (1e16, "10000000000000000")):
        atom = P(Number(whole))
        assert atom.to_unicode_str() == f"P({text})"
        assert atom.to_latex() == f"P({text})"
        assert atom.to_tptp() == f"p({text})"
        assert atom.to_prover9() == f'P("{text}")'
        assert formula_to_prolog_clause(atom) == f"p({text})."
        assert atom.to_smtlib() == P(Number(int(whole))).to_smtlib()
    # and a value with a fractional part keeps its point
    atom = P(Number(2.5))
    assert (atom.to_unicode_str(), atom.to_tptp(), atom.to_prover9()) == ("P(2.5)", "p(2.5)", 'P("2.5")')


def test_two_spellings_of_a_value_are_one_text_in_a_formula_and_in_a_problem():
    both = And(P(Number(1)), P(Number(1.0)))
    assert both.to_unicode_str() == "P(1) ∧ P(1)" and both.to_tptp() == "(p(1) & p(1))"
    assert Atom("R", (Number(1), Number(1.0))).to_tptp() == "r(1,1)"


# --------------------------------------------------------------------------- #
# The readers: a text with a point and a text without are the one numeral.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text, value, kind", [
    ("1", 1, int), ("1.0", 1, int), ("01", 1, int), ("1.00", 1, int), ("0.0", 0, int), ("-0.0", 0, int),
    ("-2.0", -2, int), ("2.50", 2.5, float), ("001.50", 1.5, float), ("0.1", 0.1, float),
    ("10000000000000000.0", 10 ** 16, int),
    # a text whose fractional digits are all zero is the integer it spells, however large: 10**23
    # (it was read through ``float`` before, as the double nearest to it, 99999999999999991611392,
    # which is another integer and merged the text with the text of that integer)
    ("100000000000000000000000.0", 10 ** 23, int),
    ("100000000000000000000000", 10 ** 23, int),                    # no point: the integer itself
    ("99999999999999991611392.0", 99999999999999991611392, int),    # and another integer is another numeral
])
def test_the_text_reader_reads_every_spelling_of_a_value_as_one_node(text, value, kind):
    result = api.parse_any(f"P({text})")
    assert result.ok, result.errors
    [term] = result.formula.args
    assert term == Number(value) and type(term.value) is kind


def test_the_other_readers_read_a_whole_float_as_the_integer():
    assert parse_prover9("P(1.0)").args == (Number(1),) and type(parse_prover9("P(1.0)").args[0].value) is int
    assert parse_prover9('P("1")').args == (Number(1),)
    [record] = parse_tptp("fof(a, axiom, p(1.0)).\n")
    assert record.formula.args == (Number(1),) and type(record.formula.args[0].value) is int
    [record] = parse_tptp("fof(a, axiom, p(-0.0)).\n")
    assert record.formula.args == (Number(0),) and type(record.formula.args[0].value) is int
    assert parse_prolog_clause("p(1.0).").args == (Number(1),)
    assert parse_prolog_clause("p(-0.0).").args == (Number(0),)
    assert parse_prolog_clause("p(2.5).").args == (Number(2.5),)


@pytest.mark.parametrize("whole", [1.0, 100.0, -0.0, 1e16])
def test_what_a_writer_writes_for_a_numeral_is_read_back_as_the_same_node(whole):
    atom = P(Number(whole))
    assert api.parse_any(atom.to_unicode_str()).formula == atom
    assert parse_prover9(atom.to_prover9()) == atom
    assert parse_prolog_clause(formula_to_prolog_clause(atom)) == atom
    [record] = parse_tptp(f"fof(a, axiom, {atom.to_tptp()}).\n")
    assert record.formula == atom


# --------------------------------------------------------------------------- #
# The routes that key an atom by its printed text read the two spellings as one atom.
# --------------------------------------------------------------------------- #

_ONE, _ONE_FLOAT, _TWO = P(Number(1)), P(Number(1.0)), P(Number(2))
_SAME = Implies(_ONE, _ONE_FLOAT)           # A -> A


def test_the_truth_table_is_a_tautology_for_one_atom_in_two_spellings():
    assert truthtable.is_tautology(_SAME)
    assert not truthtable.is_tautology(Implies(_ONE, _TWO))              # A -> B
    assert not truthtable.is_tautology(Implies(_ONE, P(Number(2.5))))    # A -> B


def test_the_intuitionistic_decision_procedures_prove_one_atom_in_two_spellings():
    assert int_valid(_SAME) and int_prove([], _SAME)
    assert int_prove([_ONE], _ONE_FLOAT) and int_prove([_ONE_FLOAT], _ONE)
    assert not int_valid(Implies(_ONE, _TWO)) and not int_prove([], Implies(_ONE, _TWO))


def test_the_intuitionistic_backend_proves_it_through_the_prove_surface():
    verdict = api.prove(_SAME, [], backends=["intuitionistic"], logic="intuitionistic", timeout=20000)
    assert verdict.status == "proved", verdict
    refuted = api.prove(Implies(_ONE, _TWO), [], backends=["intuitionistic"], logic="intuitionistic",
                        timeout=20000)
    assert refuted.status == "refuted", refuted


def test_the_counterfactual_search_finds_no_countermodel_of_one_atom_in_two_spellings():
    assert cf_valid(_SAME)
    assert not cf_valid(Implies(_ONE, _TWO))        # a verified countermodel: A true, B false


@pytest.mark.parametrize("formula", [_SAME, Implies(Box(_ONE), Box(_ONE_FLOAT)), Box(_SAME)])
def test_the_kripke_enumerator_has_no_countermodel_of_one_atom_in_two_spellings(formula):
    result = modal_enum_search(formula, max_worlds=3)
    assert result.model is None and result.exhausted and not result.unsupported, result


def test_the_kripke_enumerator_still_finds_a_countermodel_of_two_atoms():
    formula = Implies(Box(_ONE), Box(_TWO))      # two worlds: 0 sees 1, where P(1) is true and P(2) false
    result = modal_enum_search(formula, max_worlds=3)
    assert result.model is not None
    assert not satisfies_modal(formula, result.model, 0)


def test_box_p_one_entails_box_p_one_float_on_every_modal_route():
    premise, goal = Box(_ONE), Box(_ONE_FLOAT)
    assert api.prove(goal, [premise], backends=["modal-tableau"], logic="modal", timeout=20000).status == "proved"
    assert api.prove(goal, [premise], backends=["qml"], logic="modal", timeout=20000).status == "proved"
    # the bounded enumerator cannot prove, and must never refute a valid entailment
    assert api.prove(goal, [premise], backends=["kripke-enum"], logic="modal", timeout=20000).status != "refuted"
    # a control with two numerals really is refuted (two worlds: 0 sees 1, where P(1) holds and P(2) does not)
    assert api.prove(Box(_TWO), [premise], backends=["kripke-enum"], logic="modal", timeout=20000).status == "refuted"


def test_the_classical_routes_agree_that_one_atom_in_two_spellings_is_one_atom():
    for backend in ("z3", "tableau", "resolution"):
        assert api.prove(_ONE_FLOAT, [_ONE], backends=[backend], timeout=20000).status == "proved", backend
        assert api.prove(_ONE, [_ONE_FLOAT], backends=[backend], timeout=20000).status == "proved", backend
    assert api.prove(_TWO, [_ONE], backends=["z3"], timeout=20000).status == "refuted"
    one, one_float = Number(1).to_z3(), Number(1.0).to_z3()
    assert one.eq(one_float)


# --------------------------------------------------------------------------- #
# The arithmetic routes, asked for by name: an integral value is the integer under sort="int"
# and the real of that value under sort="real".
# --------------------------------------------------------------------------- #

def _tff(sort, *numbers):
    c = Constant("c")
    premise = Atom(">", [c, numbers[0]])
    goal = Atom(">", [c, numbers[1]])
    return generate_tff_arith_problem([premise], goal, sort=sort)[0]


def test_an_integral_numeral_is_an_integer_literal_under_the_int_sort():
    text = _tff("int", Number(2.0), Number(1))
    assert "c: $int" in text and "$greater(c,2)" in text and "$greater(c,1)" in text and "2.0" not in text
    assert _tff("int", Number(2.0), Number(1)) == _tff("int", Number(2), Number(1))


def test_an_integral_numeral_is_a_real_literal_under_the_real_sort():
    text = _tff("real", Number(2.0), Number(1))
    assert "c: $real" in text and "$greater(c,2.0)" in text and "$greater(c,1.0)" in text
    assert _tff("real", Number(2), Number(1.0)) == text


def test_a_numeral_with_a_fraction_has_no_integer_literal_and_is_refused_by_name():
    with pytest.raises(NotImplementedError, match="decimal point"):
        _tff("int", Number(2.5), Number(1))
    assert "$greater(c,2.5)" in _tff("real", Number(2.5), Number(1))


@pytest.mark.parametrize("sort", ["int", "real"])
def test_one_plus_one_is_two_however_the_numerals_are_spelled(sort):
    # hand-derived: 1.0 + 1.0 = 2 in the integers and in the reals, and 1.0 + 1.0 = 3 in neither
    two = Function("+", [Number(1.0), Number(1)])
    assert is_valid_arith(Atom("=", [two, Number(2)]), sort=sort)
    assert is_valid_arith(Atom("=", [two, Number(2.0)]), sort=sort)
    assert not is_valid_arith(Atom("=", [two, Number(3)]), sort=sort)


def test_the_z3_arithmetic_literal_of_a_whole_float_has_the_sort_that_was_asked_for():
    import z3

    formula = Atom("=", [Number(2.0), Constant("c")])
    assert to_z3_arith(formula, sort="int").arg(0).sort() == z3.IntSort()
    assert to_z3_arith(formula, sort="real").arg(0).sort() == z3.RealSort()



# --------------------------------------------------------------------------- #
# A bounded differential: routes that key an atom by its printed text against routes that read the
# node, over formulas whose atoms spell the same numeral two ways.
# --------------------------------------------------------------------------- #

# each pair is ONE atom in two spellings: P(1) P(1.0), P(2) P(2.0), Q(0) Q(-0.0), P(2.5) P(2.50)
_ATOM_PAIRS = [(P(Number(1)), P(Number(1.0))), (P(Number(2)), P(Number(2.0))),
               (Atom("Q", [Number(0)]), Atom("Q", [Number(-0.0)])), (P(Number(2.5)), P(Number(2.50)))]


def _random_pairs(count, seed):
    """``count`` pairs ``(g, g')``: the same random formula, ``g'`` with every atom in the other spelling
    (chosen at random per leaf), so ``g → g'`` and ``□g → □g'`` are instances of ``A → A``."""
    import random

    rng = random.Random(seed)

    def build(depth):
        if depth == 0 or rng.random() < 0.25:
            first, second = rng.choice(_ATOM_PAIRS)
            return (first, second) if rng.random() < 0.5 else (second, first)
        kind = rng.choice(["not", "and", "or", "implies", "iff"])
        if kind == "not":
            inner, twin = build(depth - 1)
            return Not(inner), Not(twin)
        (left, left_twin), (right, right_twin) = build(depth - 1), build(depth - 1)
        connective = {"and": And, "or": Or, "implies": Implies, "iff": Iff}[kind]
        return connective(left, right), connective(left_twin, right_twin)

    return [build(3) for _ in range(count)]


def test_the_truth_table_and_z3_agree_that_a_formula_implies_its_respelling():
    for formula, twin in _random_pairs(80, seed=20261005):
        instance = Implies(formula, twin)           # A -> A: a tautology
        assert truthtable.is_tautology(instance), instance.to_unicode_str()
        assert api.prove(instance, [], backends=["z3"], timeout=20000).status == "proved", instance.to_unicode_str()


def test_the_truth_table_agrees_with_z3_on_random_formulas_over_two_spellings():
    for formula, twin in _random_pairs(100, seed=20261007):
        for candidate in (formula, Not(twin)):
            table = truthtable.is_tautology(candidate)
            status = api.prove(candidate, [], backends=["z3"], timeout=20000).status
            assert status in ("proved", "refuted") and table == (status == "proved"), candidate.to_unicode_str()


def test_the_modal_routes_agree_that_a_boxed_formula_entails_its_respelling():
    for formula, twin in _random_pairs(25, seed=20261006):
        premise, goal = Box(formula), Box(twin)     # □A ⊢ □A
        assert api.prove(goal, [premise], backends=["modal-tableau"], logic="modal",
                         timeout=20000).status == "proved", premise.to_unicode_str()
        result = modal_enum_search(Implies(premise, goal), max_worlds=2)
        assert result.model is None and not result.unsupported, premise.to_unicode_str()
