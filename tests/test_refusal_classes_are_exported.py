"""The exception classes the public functions raise can be imported where the functions are.

``analyse_signatures`` (and the third-order parser and writers) raise ``NestedPropertySlotError`` for a
predicate of properties that sits in a property slot, next to ``MixedSlotError``; the four second-order
searches raise ``CandidateBoundExceeded`` at a domain size with more candidates than ``max_candidates``. A
caller that wants to catch one of them finds it in the package the function came from.
"""

import pytest

import unicode_logic_kit
import unicode_logic_kit.fol
import unicode_logic_kit.fol.nodes
import unicode_logic_kit.semantics
from unicode_logic_kit.fol._ho_nodes import NestedPropertySlotError
from unicode_logic_kit.semantics.secondorder import CandidateBoundExceeded


@pytest.mark.parametrize("package", [unicode_logic_kit, unicode_logic_kit.fol, unicode_logic_kit.fol.nodes])
def test_the_nested_property_slot_refusal_is_exported_next_to_the_mixed_slot_refusal(package):
    assert package.NestedPropertySlotError is NestedPropertySlotError
    assert "NestedPropertySlotError" in package.__all__ and "MixedSlotError" in package.__all__


@pytest.mark.parametrize("package", [unicode_logic_kit, unicode_logic_kit.semantics])
def test_the_candidate_bound_refusal_is_exported_next_to_the_searches(package):
    assert package.CandidateBoundExceeded is CandidateBoundExceeded
    assert "CandidateBoundExceeded" in package.__all__ and "so_find_model" in package.__all__


def test_both_are_caught_as_the_classes_a_caller_already_catches():
    from unicode_logic_kit.fol.naming import ParsingError
    assert issubclass(NestedPropertySlotError, ParsingError)
    assert issubclass(CandidateBoundExceeded, ValueError)
