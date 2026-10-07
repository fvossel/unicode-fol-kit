"""An SMT-LIB symbol of an arithmetic sort is a symbol, whatever its name.

The kit writes a numeral as a symbol of its uninterpreted sort, named by the numeral's text, and the reader
reads such a symbol back as the numeral. A text over ``Int`` or ``Real`` has numerals of its own, and there a
declared symbol named ``1`` is another term than the numeral ``1``:

    (declare-fun |1| () Int)
    (assert (not (= |1| 1)))

is satisfiable (take the symbol to be 0: 0 is not 1). Read with both terms as the number 1 the assertion is
``¬ 1 = 1``, which nothing satisfies, and everything follows from it: a wrong ``proved``. The reader keeps the
two apart (a constant named ``1`` next to the numeral 1), and the routes that cannot keep a constant and a
numeral of one text apart refuse the pair by name.
"""

import z3

from unicode_logic_kit import api
from unicode_logic_kit.atp.z3_input import parse_smtlib, to_smtlib
from unicode_logic_kit.fol.nodes import Atom, Constant, Not, Number

INT_TEXT = "(declare-fun |1| () Int)\n(assert (not (= |1| 1)))\n"
REAL_TEXT = "(declare-fun |2.5| () Real)\n(assert (not (= |2.5| 2.5)))\n"


def test_the_text_itself_is_satisfiable():
    solver = z3.Solver()
    solver.from_string(INT_TEXT)
    assert solver.check() == z3.sat


def test_an_int_symbol_named_like_a_numeral_is_read_as_a_constant():
    assert parse_smtlib(INT_TEXT) == [Not(Atom("=", [Constant("1"), Number(1)]))]


def test_a_real_symbol_named_like_a_numeral_is_read_as_a_constant():
    assert parse_smtlib(REAL_TEXT) == [Not(Atom("=", [Constant("2.5"), Number(2.5)]))]


def test_nothing_is_proved_from_the_satisfiable_text():
    # ⊥ follows from a set of assertions only if nothing satisfies them, and the text is satisfiable
    verdict = api.prove(Atom("⊥", []), parse_smtlib(INT_TEXT), backends=["z3"], timeout=8000)
    assert verdict.status != "proved", verdict
    assert verdict.status == "unknown" and "numeral 1 and a constant named '1'" in verdict.detail


def test_a_numeral_the_kit_wrote_reads_back_as_the_numeral():
    # the writer's own text: the numeral is a symbol of the uninterpreted sort
    for value in (0, 1, 42):
        assert parse_smtlib(to_smtlib(Atom("P", [Number(value)]))) == [Atom("P", [Number(value)])]


def test_a_symbol_of_any_uninterpreted_sort_named_like_a_numeral_is_the_numeral():
    text = "(declare-sort U 0)\n(declare-fun |7| () U)\n(declare-fun Q (U) Bool)\n(assert (Q |7|))\n"
    assert parse_smtlib(text) == [Atom("Q", [Number(7)])]
