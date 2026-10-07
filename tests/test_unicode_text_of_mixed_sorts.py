"""Which nodes have a text form: a node that mixes sorted and unsorted occurrences has none.

The many-sorted text grammar is all-sorted or all-unsorted: every quantifier carries a sort
(``∀x:A``) and every constant does (``carl:A``), or none does. A node can mix the two, because
the kit's semantics allows it (``c:S`` and plain ``c`` are one constant, an unsorted variable ranges
over the whole universe), and ``to_unicode_str`` prints such a node anyway. The printed text then
reads back in no parser mode, and that failure is LOUD: it is never read as a different formula.

Hand-derived: of the eight nodes ``Q1 x Q2 y P(x, y, c)`` with ``Q1`` sorted or not, ``Q2`` sorted or
not and ``c`` sorted or not, exactly two are uniform (all sorted, all unsorted) and read back to the
same node; the other six mix and are refused.
"""

import itertools

import pytest

from unicode_logic_kit import MSFLParser, NamingError, api
from unicode_logic_kit.fol._msfl_nodes import SortedConstant, SortedQuantifier
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Node, Quantifier, Variable

X, Y = Variable("x"), Variable("y")

MODES = {"fol": {}, "msfol": {"many_sorted": True}, "msfl": {"many_sorted": True, "fuzzy": True},
         "modal": {"modal": True}, "msfol+modal": {"many_sorted": True, "modal": True}}


def _node(outer_sorted, inner_sorted, constant_sorted):
    body = Atom("P", [X, Y, SortedConstant("carl", "C") if constant_sorted else Constant("carl")])
    inner = SortedQuantifier("∃", Y, "B", body) if inner_sorted else Quantifier("∃", Y, body)
    return SortedQuantifier("∀", X, "A", inner) if outer_sorted else Quantifier("∀", X, inner)


COMBINATIONS = list(itertools.product((False, True), repeat=3))


def _read(text, kwargs):
    return MSFLParser(**kwargs).parse(text)


@pytest.mark.parametrize("combination", COMBINATIONS, ids=lambda c: "".join("S" if s else "u" for s in c))
def test_a_uniform_node_reads_back_and_a_mixed_one_is_refused_in_every_mode(combination):
    node = _node(*combination)
    text = node.to_unicode_str()
    uniform = len(set(combination)) == 1
    outcomes = {}
    for mode, kwargs in MODES.items():
        try:
            outcomes[mode] = _read(text, kwargs)
        except NamingError:
            outcomes[mode] = None
    if uniform:
        # the all-sorted text reads in the many-sorted modes, the all-unsorted one in the others
        assert any(back == node for back in outcomes.values()), text
    else:
        assert outcomes == {mode: None for mode in MODES}, text          # refused everywhere
    # Never read as a different formula, in any mode.
    assert all(back is None or back == node for back in outcomes.values()), text
    assert api.parse_any(text).ok is uniform


def test_the_three_nodes_that_were_reported_are_refused_by_name():
    cases = [
        SortedQuantifier("∀", X, "A", Quantifier("∃", Y, Atom("P", [X, Y]))),     # ∀x:A ∃y P(x, y)
        And(Atom("P", [SortedConstant("carl", "A")]), Atom("Q", [Constant("carl")])),
        Quantifier("∀", X, Atom("P", [X, SortedConstant("carl", "A")])),
    ]
    for node in cases:
        text = node.to_unicode_str()
        assert isinstance(node, Node)
        for kwargs in MODES.values():
            with pytest.raises(NamingError):
                _read(text, kwargs)
        assert api.parse_any(text).ok is False


def test_the_docstring_says_which_nodes_have_no_text_form():
    doc = Node.to_unicode_str.__doc__
    assert "mixes sorted and unsorted" in doc
    assert "NamingError" in doc and "never" in doc
