"""The checks of whether a structure is a structure of the many-sorted definition are public.

``IllegalStructureError``, ``check_structure`` and ``structure_violations`` live in
``semantics.tarski`` and are exported from ``unicode_logic_kit.semantics`` (and listed in the API
reference, which ``test_api_reference_complete`` enforces name by name).
"""

import pytest

import unicode_logic_kit.semantics as semantics
from unicode_logic_kit.fol.nodes import Atom, Constant, SortedConstant
from unicode_logic_kit.semantics import (
    IllegalStructureError, Structure, check_structure, structure_violations,
)
from unicode_logic_kit.semantics import tarski

NAMES = ("IllegalStructureError", "check_structure", "structure_violations")


@pytest.mark.parametrize("name", NAMES)
def test_the_name_is_exported_and_is_the_one_of_tarski(name):
    assert name in semantics.__all__
    assert getattr(semantics, name) is getattr(tarski, name)


def test_the_error_is_a_value_error():
    assert issubclass(IllegalStructureError, ValueError)


def test_a_structure_of_the_definition_has_no_violation():
    legal = Structure([0, 1], constants={"carl": 0}, sorts={"Human": (0,)})
    assert structure_violations(legal, Atom("Mortal", [SortedConstant("carl", "Human")])) == []
    check_structure(legal, Atom("Mortal", [SortedConstant("carl", "Human")]))        # returns None


def test_an_empty_sort_and_a_sorted_constant_outside_its_sort_are_named():
    # Human = {} (a sort is never empty); carl denotes 1 but Animal = {0}
    illegal = Structure([0, 1], constants={"carl": 1}, sorts={"Human": (), "Animal": (0,)})
    formula = Atom("Mortal", [SortedConstant("carl", "Animal")])
    problems = structure_violations(illegal, formula)
    assert any("Human" in p and "empty" in p for p in problems)
    assert any("carl" in p and "Animal" in p for p in problems)
    with pytest.raises(IllegalStructureError) as caught:
        check_structure(illegal, formula)
    assert "Human" in str(caught.value)
