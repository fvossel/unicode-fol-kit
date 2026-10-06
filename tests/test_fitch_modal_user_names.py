"""The modal line checker of the Fitch module and a variable spelled like a world variable.

The checker translates a line and its open assumptions one by one (the standard translation,
current world ``w``) and asks whether the assumptions' images entail the line's image. A user
variable may have any spelling, also ``w`` (the current world of the translation), ``w0``
(the first world a box binds) or ``x0`` (the name a variable spelled ``w`` is moved to). The
verdicts below are derived by hand from what the formulas say: two different free variables
are two unknown elements, so nothing about one follows from the other; one variable is the
same element wherever it stands.
"""
import pytest

from unicode_fol_kit.atp.fitch import _make_modal_checker
from unicode_fol_kit.fol.nodes import Atom, Box, Variable


def P(name):
    return Atom("P", [Variable(name)])


ROWS = [
    # The same element on both sides.
    ("P(w) |- P(w)", [P("w")], P("w"), True),
    ("[]P(w) |- []P(w)", [Box(P("w"))], Box(P("w")), True),
    ("P(w), P(x0) |- P(w)", [P("w"), P("x0")], P("w"), True),
    ("P(w0) |- P(w0)", [P("w0")], P("w0"), True),
    # Two elements: P may hold of one and not of the other.
    ("P(w) |- P(x0)", [P("w")], P("x0"), False),
    ("P(x0) |- P(w)", [P("x0")], P("w"), False),
    ("[]P(w) |- []P(w0)", [Box(P("w"))], Box(P("w0")), False),
    ("[]P(w0) |- []P(w1)", [Box(P("w0"))], Box(P("w1")), False),
    # In K a box does not give the fact at the current world, whatever the variable is called.
    ("[]P(w) |- P(w)", [Box(P("w"))], P("w"), False),
]


@pytest.mark.parametrize("name, assumptions, line, expected", ROWS, ids=[row[0] for row in ROWS])
def test_a_line_follows_exactly_when_the_formulas_say_so(name, assumptions, line, expected):
    accepted, reason = _make_modal_checker("K")(assumptions, line)
    assert accepted is expected, reason


def test_reflexive_frames_give_the_fact_under_a_box_for_a_variable_named_like_the_world():
    accepted, reason = _make_modal_checker("T")([Box(P("w"))], P("w"))
    assert accepted is True, reason
    accepted, reason = _make_modal_checker("T")([Box(P("w"))], P("x0"))
    assert accepted is False
