r"""What the Prover9 reader does with a numeral it would merge with another, and with a formula nested
deeper than Python can recurse.

**Bare numerals.** Prover9 keeps ``01`` and ``1`` apart as two constants (and ``1.0`` and ``1``, ``2.50``
and ``2.5``): the file ``P(01). -P(1).`` is consistent (U = {0, 1}, 01 = 0, 1 = 1, P = {0}). A ``Number``
node is identified by its value and has one text, so reading both as one numeral would make the file say
about one constant what it says about two, and ``P(1)``, ``¬P(1)`` prove everything. A text that spells one
numeral value two ways, in one formula or in two formulas of a file, is refused by name; a numeral that
stands alone in its text is read as the number it spells.

**Depth.** The reader transforms the parse tree with an explicit stack, so a chain of operands (``a | b |
c | ...`` is a left-nested tree) or a stack of negations or quantifiers is read at any depth the parser
itself reads. What the interpreter still cannot recurse through is the reader's own parse error, never a
bare ``RecursionError``.
"""

import pytest

from unicode_fol_kit.fol import prover9_input as reader
from unicode_fol_kit.fol.nodes import Atom, Constant, Not, Number, Or, Quantifier
from unicode_fol_kit.fol.prover9_input import Prover9ParsingError, parse_prover9, parse_prover9_problem

a = Constant("a")


def P(*args):
    return Atom("P", list(args))


@pytest.mark.parametrize("text", ["P(01) & Q(1)", "P(1.0) & Q(1)", "P(2.50) | Q(2.5)", "P(-0) & Q(0)",
                                  "P(007) & P(7)", 'P("1") & Q(01)', "(a = 01) -> P(f(1))", "P(1.0, 1)"])
def test_the_reader_refuses_a_text_that_spells_one_numeral_two_ways(text):
    with pytest.raises(Prover9ParsingError) as refused:
        parse_prover9(text)
    assert "one text" in str(refused.value) and "numerals" in str(refused.value)


@pytest.mark.parametrize("text", ["P(01) & Q(01)", "P(01) & Q(2)", "P(1) & Q(1)", "P(1.0) & Q(2.0)", "P(1, 2, 3)",
                                  "P(0.1) & Q(0.1 + 1)"])
def test_the_reader_reads_numerals_that_are_one_spelling_each(text):
    # Each value is spelled one way in the text (1.0 and 2.0 are two values; 0.1 and 1 are two values).
    parse_prover9(text)


@pytest.mark.parametrize("text, value", [("P(0)", 0), ("P(1)", 1), ("P(-1)", -1), ("P(2.5)", 2.5), ("P(10)", 10),
                                         ("P(0.1)", 0.1), ("P(-2.5)", -2.5), ("P(100)", 100), ("P(01)", 1),
                                         ("P(100.0)", 100.0)])
def test_a_numeral_that_stands_alone_is_read_as_the_number_it_spells(text, value):
    assert parse_prover9(text) == P(Number(value))


def test_a_file_that_keeps_01_and_1_apart_is_refused_not_merged():
    text = "\n".join([
        "formulas(assumptions).", "  P(01).", "  -P(1).", "end_of_list.",
        "formulas(goals).", "  Q(alpha).", "end_of_list.", ""])
    with pytest.raises(Prover9ParsingError) as refused:
        parse_prover9_problem(text)
    assert "01" in str(refused.value) and "numerals 1 and 01" in str(refused.value)


def test_a_file_that_writes_each_numeral_one_way_is_read():
    text = "\n".join([
        "formulas(assumptions).", "  P(01).", "  Q(01, 2).", "end_of_list.",
        "formulas(goals).", "  P(01).", "end_of_list.", ""])
    assert len(parse_prover9_problem(text)) == 3


def test_a_chain_of_hundreds_of_disjuncts_is_read():
    node = parse_prover9(" | ".join(["P(a)"] * 600))
    spine = 0
    while isinstance(node, Or):
        assert node.right == P(a)
        node = node.left
        spine += 1
    assert spine == 599 and node == P(a)


def test_a_stack_of_hundreds_of_negations_is_read():
    node = parse_prover9("-(" * 800 + "P(a)" + ")" * 800)
    depth = 0
    while isinstance(node, Not):
        node = node.formula
        depth += 1
    assert depth == 800 and node == P(a)


def test_a_stack_of_hundreds_of_quantifiers_is_read():
    node = parse_prover9("(all X " * 500 + "P(X)" + ")" * 500)
    depth = 0
    while isinstance(node, Quantifier):
        node = node.formula
        depth += 1
    assert depth == 500


def test_a_recursion_limit_in_the_parser_is_the_readers_own_parse_error(monkeypatch):
    def too_deep(*args, **kwargs):
        raise RecursionError("maximum recursion depth exceeded")

    monkeypatch.setattr(reader._PARSER, "parse", too_deep)
    with pytest.raises(Prover9ParsingError) as refused:
        parse_prover9("P(a)")
    assert "nested too deeply" in str(refused.value)


def test_a_recursion_limit_in_the_transformation_is_the_readers_own_parse_error(monkeypatch):
    def too_deep(*args, **kwargs):
        raise RecursionError("maximum recursion depth exceeded")

    monkeypatch.setattr(reader, "_transform_tree", too_deep)
    with pytest.raises(Prover9ParsingError) as refused:
        parse_prover9("P(a)")
    assert "nested too deeply" in str(refused.value)
    with pytest.raises(Prover9ParsingError):
        parse_prover9_problem("formulas(assumptions).\n  P(a).\nend_of_list.\n")
