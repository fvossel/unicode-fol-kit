"""A name used at two arities, and a prover that types a symbol by its name alone.

The kit reads the constant ``ff`` and the unary function ``ff(x)`` as two symbols; so do
the TPTP writer and every prover it feeds but Twee, which stops on a problem that has both
(``Type mismatch in term 'ff': Constant ff has arity 1 but was applied to 0 arguments``).
The Twee route writes each arity but the first of such a name under a name of its own,
that no symbol of the problem has, and hands everything Twee prints back under the name the
caller used, so the question Twee answers is the question that was asked.

Hand-derived verdicts, over the universe ``{0, 1}`` where a countermodel is needed:

* ``ff = aa``, ``∀x ff(x) = x`` entail ``ff(aa) = aa`` (the second premise at ``aa``).
* ``ff = aa``, ``∀x ff(x) = bb`` do not entail ``aa = bb`` (the constant ``ff`` and ``aa`` are
  0, the function ``ff`` is constantly 1, ``bb`` is 1) and do not entail ``ff = bb``.
* ``∀x ff(x) = bb``, ``ff = aa`` entail ``ff(ff) = bb`` (the first premise at the constant ``ff``).
* ``ff(aa) = bb``, ``∀x ∀y ff(x, y) = x`` entail ``ff(aa, cc) = aa`` and do not entail
  ``ff(aa, cc) = bb`` (``aa`` is 0, ``bb`` is 1, the unary ``ff`` maps 0 to 1).
"""

import re

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import twee_entailment as te
from unicode_logic_kit.atp.protocol import get_backend
from unicode_logic_kit.atp.twee_backend import TweeBackend
from unicode_logic_kit.fol._identifiers import symbol_names
from unicode_logic_kit.fol.nodes import (
    Atom, Constant, Function, Measure, Quantifier, SortedConstant, Variable,
)
from unicode_logic_kit.fol.tptp_input import parse_tptp

_X, _Y = Variable("x"), Variable("y")
_AA, _BB, _CC, _FF = (Constant(name) for name in ("aa", "bb", "cc", "ff"))


def _app(name, *args):
    return Function(name, list(args))


def _eq(left, right):
    return Atom("=", [left, right])


def _all(*variables_and_body):
    *variables, body = variables_and_body
    for variable in reversed(variables):
        body = Quantifier("∀", variable, body)
    return body


# ff = aa   and   ∀x ff(x) = x
_CONSTANT_FF = _eq(_FF, _AA)
_UNARY_FF_IS_IDENTITY = _all(_X, _eq(_app("ff", _X), _X))
_UNARY_FF_IS_BB = _all(_X, _eq(_app("ff", _X), _BB))


def _arities(formulas):
    return te._symbol_arities(list(formulas))


# ---------------------------------------------------------------------------
# The census of arities and the separation
# ---------------------------------------------------------------------------

def test_the_arities_of_a_name_are_listed_in_the_order_they_first_occur():
    formulas = [_CONSTANT_FF, _UNARY_FF_IS_IDENTITY,
                _eq(_app("gg", _app("ff", _AA), _BB), SortedConstant("cc", "Sort"))]
    assert _arities(formulas) == {"ff": [0, 1], "aa": [0], "gg": [2], "bb": [0], "cc": [0]}


def test_a_constant_a_sorted_constant_and_a_function_of_no_arguments_are_one_symbol():
    formulas = [_eq(Constant("zz"), SortedConstant("zz", "Sort")), _eq(Function("zz", []), _AA)]
    assert _arities(formulas) == {"zz": [0], "aa": [0]}


def test_a_problem_that_uses_every_name_at_one_arity_is_left_alone():
    formulas = [_CONSTANT_FF, _all(_X, _eq(_app("gg", _X), _X))]
    separated, restore = te._separate_arities(formulas)
    assert separated is formulas and restore == {}


@pytest.mark.parametrize("formulas", [
    [_CONSTANT_FF, _UNARY_FF_IS_IDENTITY],
    [_UNARY_FF_IS_IDENTITY, _CONSTANT_FF],
    [_eq(_app("ff", _AA), _BB), _all(_X, _Y, _eq(_app("ff", _X, _Y), _X)), _eq(_FF, _CC)],
    [_eq(_app("ff", _AA), _BB), _eq(Constant("ff"), _AA), _all(_X, _Y, _eq(_app("ff", _X, _Y), _X))],
], ids=["constant first", "function first", "three arities", "three arities, constant second"])
def test_every_arity_of_a_name_ends_up_with_a_name_of_its_own_and_nothing_else_changes(formulas):
    separated, restore = te._separate_arities(formulas)
    assert all(len(seen) == 1 for seen in _arities(separated).values())
    # one symbol per arity: the same number of symbols (name, arity) before and after
    assert (sum(len(seen) for seen in _arities(formulas).values())
            == sum(len(seen) for seen in _arities(separated).values()))
    # the minted names are the keys of the table and are not names of the problem
    problem_names = {name.casefold() for name in symbol_names(*formulas)}
    assert all(minted.casefold() not in problem_names for minted in restore)
    assert len({minted.casefold() for minted in restore}) == len(restore)
    # and what the table undoes is exactly the renaming: every atom comes back as it was
    for before, after in zip(formulas, separated):
        while isinstance(before, Quantifier):
            before, after = before.formula, after.formula
        assert Atom("=", [te._restore_term_names(arg, restore) for arg in after.args]) == before


def test_the_first_arity_keeps_its_name_and_the_others_get_a_new_one():
    constant_first, restore = te._separate_arities([_CONSTANT_FF, _UNARY_FF_IS_IDENTITY])
    assert constant_first[0] == _CONSTANT_FF
    assert set(restore.values()) == {"ff"} and len(restore) == 1
    function_first, restore = te._separate_arities([_UNARY_FF_IS_IDENTITY, _CONSTANT_FF])
    assert function_first[0] == _UNARY_FF_IS_IDENTITY
    assert function_first[1].args[0] != _FF and set(restore.values()) == {"ff"}


def _first_minted_name():
    """The name the separation gives the unary ``ff`` of ``ff = aa`` and ``∀x ff(x) = x`` when
    nothing else of the problem is in its way."""
    _separated, restore = te._separate_arities([_CONSTANT_FF, _UNARY_FF_IS_IDENTITY])
    (minted,) = restore
    return minted


_TAKEN_NAMES = {
    "the same word": lambda minted: (minted,),
    "the word capitalised": lambda minted: (minted.capitalize(),),
    "the word in upper case": lambda minted: (minted.upper(),),
    "the word and its successor": lambda minted: (minted, minted + "_1"),
    "the word capitalised and its successor in upper case": lambda minted: (
        minted.capitalize(), (minted + "_1").upper()),
}


@pytest.mark.parametrize("label", sorted(_TAKEN_NAMES))
def test_a_minted_name_is_not_a_name_of_the_problem_in_any_kind_or_case(label):
    """The first names the separation would try are, in turn, a function, a constant, a
    predicate and a sort of the problem; whatever they are, and however their case differs
    from the minted one's (TPTP reads ``Ff_arity1`` and ``ff_arity1`` as one word), the
    minted name is another."""
    taken = _TAKEN_NAMES[label](_first_minted_name())
    kinds = (lambda name: _eq(_app(name, _AA), _BB), lambda name: _eq(Constant(name), _AA),
             lambda name: Atom(name, [_AA]), lambda name: Atom("P", [SortedConstant("dd", name)]))
    for kind in kinds:
        formulas = [_CONSTANT_FF, _UNARY_FF_IS_IDENTITY] + [kind(name) for name in taken]
        _separated, restore = te._separate_arities(formulas)
        assert len(restore) == 1
        (minted,) = restore
        assert minted.casefold() not in {name.casefold() for name in symbol_names(*formulas)}


def test_a_function_of_no_arguments_that_is_renamed_is_the_constant_of_its_new_name():
    formulas = [_UNARY_FF_IS_IDENTITY, _eq(Function("ff", []), _AA)]
    separated, restore = te._separate_arities(formulas)
    (minted,) = restore
    assert separated[1] == _eq(Constant(minted), _AA)
    assert te._restore_term_names(Constant(minted), restore) == Constant("ff")


def test_a_sorted_constant_that_is_renamed_keeps_its_sort():
    formulas = [_UNARY_FF_IS_IDENTITY, _eq(SortedConstant("ff", "Sort"), _AA)]
    separated, restore = te._separate_arities(formulas)
    (minted,) = restore
    assert separated[1] == _eq(SortedConstant(minted, "Sort"), _AA)


def test_a_measure_is_the_binary_function_measure():
    measure = Measure(_AA, _BB)
    unary = _eq(_app("measure", _AA), _CC)
    assert _arities([_eq(measure, _CC), unary]) == {
        "measure": [2, 1], "aa": [0], "bb": [0], "cc": [0]}
    measure_first, restore = te._separate_arities([_eq(measure, _CC), unary])
    (minted,) = restore
    assert measure_first[0] == _eq(measure, _CC)
    assert measure_first[1] == _eq(_app(minted, _AA), _CC)
    measure_second, restore = te._separate_arities([unary, _eq(measure, _CC)])
    (minted,) = restore
    assert measure_second[1] == _eq(_app(minted, _AA, _BB), _CC)
    assert te._restore_term_names(measure_second[1].args[0], restore) == _app("measure", _AA, _BB)


def test_a_symbol_that_is_not_part_of_a_clash_is_left_as_it_is():
    """``gg`` is used at two arities; the sorted constant ``cc:Sort`` and the function of no
    arguments ``zz()`` are not, and stay the very nodes they were."""
    untouched = [_eq(SortedConstant("cc", "Sort"), _AA), _eq(Function("zz", []), _BB)]
    formulas = [_all(_X, _eq(_app("gg", _X), _X)), _eq(Constant("gg"), _AA)] + untouched
    separated, restore = te._separate_arities(formulas)
    assert len(restore) == 1
    assert separated[2:] == untouched


def test_two_names_that_differ_in_case_are_each_given_a_name_of_their_own():
    formulas = [_eq(Constant("Ff"), _AA), _all(_X, _eq(_app("Ff", _X), _X)),
                _eq(_FF, _AA), _all(_X, _eq(_app("ff", _X), _X))]
    _separated, restore = te._separate_arities(formulas)
    assert sorted(restore.values()) == ["Ff", "ff"]
    assert len({minted.casefold() for minted in restore}) == 2


@pytest.mark.parametrize("name", ["Foo", "świątek", "9lives", "ab1", "Ab1_2"])
def test_a_minted_name_is_a_word_the_writer_leaves_alone(name):
    """Whatever the spelling of the name that is used at two arities (a non-ASCII or digit-leading
    one, an upper-case one), the name minted for its second arity is already a TPTP word, so the
    writer leaves it as it is, the text Twee prints speaks of it as written and the table finds
    it."""
    premises = [_eq(Constant(name), _AA), _all(_X, _eq(_app(name, _X), _X))]
    problem, name_map, restore = te._twee_problem(premises, _eq(_app(name, _AA), _AA))
    (minted,) = restore
    assert name_map.term[minted] == minted
    parsed = [statement.formula for statement in parse_tptp(problem)]
    assert all(len(seen) == 1 for seen in _arities(parsed).values()), problem


# ---------------------------------------------------------------------------
# What Twee is given, and what it is handed back as
# ---------------------------------------------------------------------------

_PROOF_OF_THE_SECOND_PREMISE = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_2): UNARY(X) = X.

Goal 1 (goal): UNARY(aa) = aa.
Proof:
  UNARY(aa)
= { by axiom 1 (premise_2) }
  aa

RESULT: Theorem (the conjecture is true).
"""


@pytest.fixture()
def twee_for_ff_problem(monkeypatch):
    """A runner that answers the problem ``ff = aa``, ``∀x ff(x) = x`` ⊢ ``ff(aa) = aa`` as Twee
    does (the proof of the goal by the second premise), with the unary function under whatever
    name the problem text gives it, and keeps the texts it was given."""
    problems = []

    def spawn(problem, **kwargs):
        problems.append(problem)
        match = re.search(r"fof\(premise_2, axiom, \(!\[X\]: \((\w+)\(X\) = X\)\)\)\.", problem)
        assert match, problem
        return _PROOF_OF_THE_SECOND_PREMISE.replace("UNARY", match.group(1)), "", False

    monkeypatch.setattr(te, "_spawn_twee", spawn)
    return problems


def test_the_problem_text_handed_to_twee_has_no_name_at_two_arities(twee_for_ff_problem):
    te.check_entailment_twee_detailed([_CONSTANT_FF, _UNARY_FF_IS_IDENTITY],
                                      _eq(_app("ff", _AA), _AA))
    (problem,) = twee_for_ff_problem
    parsed = [statement.formula for statement in parse_tptp(problem)]
    assert len(parsed) == 3
    assert all(len(seen) == 1 for seen in _arities(parsed).values()), problem


def test_the_proof_and_the_text_twee_prints_come_back_under_the_callers_names(twee_for_ff_problem):
    result = te.check_entailment_twee_detailed([_CONSTANT_FF, _UNARY_FF_IS_IDENTITY],
                                               _eq(_app("ff", _AA), _AA))
    assert result["status"] == "Theorem"
    proof = result["proof"]
    assert proof.axioms[0].equation.lhs == _app("ff", Variable("X"))
    assert proof.goal.equation.lhs == _app("ff", _AA)
    assert proof.goal.chain.terms == (_app("ff", _AA), _AA)
    assert "ff(X) = X" in result["raw_output"] and "ff(aa) = aa" in result["raw_output"]
    assert "arity" not in result["raw_output"]


def test_a_non_ascii_name_at_two_arities_comes_back_as_the_callers_name(twee_for_ff_problem):
    name = "świątek"
    result = te.check_entailment_twee_detailed(
        [_eq(Constant(name), _AA), _all(_X, _eq(_app(name, _X), _X))], _eq(_app(name, _AA), _AA))
    assert result["status"] == "Theorem"
    assert result["proof"].goal.equation.lhs == _app(name, _AA)
    assert "świątek(X) = X" in result["raw_output"]
    assert "świątek(aa) = aa" in result["raw_output"]


def test_the_backend_proves_the_problem_and_checks_the_proof_against_the_callers_premises(
        twee_for_ff_problem):
    verdict = TweeBackend().decide(_eq(_app("ff", _AA), _AA), [_CONSTANT_FF, _UNARY_FF_IS_IDENTITY])
    assert verdict.status == "proved", (verdict.reason, verdict.detail)
    assert "independently verified" in verdict.detail


def test_a_problem_without_such_a_name_is_written_as_it_always_was():
    premises = [_all(_X, _eq(_app("ff", _X), _X))]
    conclusion = _eq(_app("ff", _AA), _AA)
    assert te._generate_twee_input(premises, conclusion) == "\n".join([
        "fof(premise_1, axiom, (![X]: (ff(X) = X))).",
        "fof(goal, conjecture, (ff(aa) = aa)).", ""])


# ---------------------------------------------------------------------------
# Real Twee, through WSL
# ---------------------------------------------------------------------------

needs_twee = pytest.mark.skipif(not te.twee_available(), reason="no Twee binary reachable via WSL")

_LIVE = {
    "the second premise at aa": ([_CONSTANT_FF, _UNARY_FF_IS_IDENTITY], _eq(_app("ff", _AA), _AA),
                                 "proved"),
    "the constant ff as the argument of the function ff": (
        [_UNARY_FF_IS_BB, _CONSTANT_FF], _eq(_app("ff", _FF), _BB), "proved"),
    "two names forced equal": ([_CONSTANT_FF, _UNARY_FF_IS_BB], _eq(_AA, _BB), "refuted"),
    "the constant is not the value": ([_CONSTANT_FF, _UNARY_FF_IS_BB], _eq(_FF, _BB), "refuted"),
    "one and two arguments": (
        [_eq(_app("ff", _AA), _BB), _all(_X, _Y, _eq(_app("ff", _X, _Y), _X))],
        _eq(_app("ff", _AA, _CC), _AA), "proved"),
    "one and two arguments, not entailed": (
        [_eq(_app("ff", _AA), _BB), _all(_X, _Y, _eq(_app("ff", _X, _Y), _X))],
        _eq(_app("ff", _AA, _CC), _BB), "refuted"),
}


def _cases_named_like_a_minted_name():
    """The unary ``ff`` is ``bb`` everywhere and the user's own unary function, named like the
    word the separation would try first (as it is, and in another case), is ``cc`` everywhere:
    nothing makes ``bb`` and ``cc`` one element (universe {0, 1}, ``bb`` 0, ``cc`` 1), unless the
    two functions were one symbol."""
    minted = _first_minted_name()
    return {
        "a function named like a minted name": (
            [_CONSTANT_FF, _UNARY_FF_IS_BB, _all(_X, _eq(_app(minted, _X), _CC))],
            _eq(_BB, _CC), "refuted"),
        "a function named like a minted name, in another case": (
            [_CONSTANT_FF, _UNARY_FF_IS_BB, _all(_X, _eq(_app(minted.capitalize(), _X), _CC))],
            _eq(_BB, _CC), "refuted"),
    }


_LIVE_LABELS = sorted(list(_LIVE) + [
    "a function named like a minted name", "a function named like a minted name, in another case"])


def _live_case(label):
    return _LIVE[label] if label in _LIVE else _cases_named_like_a_minted_name()[label]


@needs_twee
@pytest.mark.parametrize("label", _LIVE_LABELS)
def test_live_twee_answers_a_problem_with_a_name_at_two_arities(label):
    premises, conclusion, expected = _live_case(label)
    verdict = api.prove(conclusion, premises, backends=["twee"], timeout=30000)
    assert verdict.status == expected, (verdict.status, verdict.reason, verdict.detail)
    if expected == "proved":
        assert "independently verified" in verdict.detail


needs_vampire = pytest.mark.skipif(
    not get_backend("vampire").available_for({"tff": False}),
    reason="no Vampire reachable for the untyped text")


@needs_vampire
@pytest.mark.parametrize("label", _LIVE_LABELS)
def test_a_prover_that_reads_the_two_symbols_apart_never_says_the_opposite(label):
    """The hand value of each case against a second prover: Vampire reads the fof text, in which
    the arities of a name are symbols of their own, so it never answers the opposite of it."""
    premises, conclusion, expected = _live_case(label)
    opposite = "refuted" if expected == "proved" else "proved"
    assert api.prove(conclusion, premises, backends=["vampire"], timeout=30000,
                     tff=False).status != opposite
