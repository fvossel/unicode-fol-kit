"""Many-sorted (MSFOL) finite model finding.

The model finder now enumerates a non-empty universe per named sort, places sorted
constants inside their sort, and lets a SortedQuantifier range over its sort — so it
finds genuine sorted structures (with a ``sorts`` mapping) and decides sorted
entailments by the absence of a sorted counter-model. Hand-checked against sorted
(in)validities; the unsorted FOL behaviour is unchanged.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.semantics.modelfinder import (
    find_model, find_countermodel, is_satisfiable_finite, is_valid_finite,
)

_S = MSFLParser(many_sorted=True)
_F = MSFLParser()


def test_sorted_model_has_sort_universes():
    theory = [_S.parse("∀x:Human Mortal(x)"), _S.parse("Human(alice:Human)")]
    m = find_model(theory, max_size=3)
    assert m is not None
    assert "Human" in m.sorts and len(m.sorts["Human"]) >= 1
    # alice is placed inside the Human sort.
    assert m.constants["alice"] in m.sorts["Human"]


def test_sorted_constant_makes_entailment_valid():
    # alice:Human is a Human, so ∀x:Human Mortal(x) entails Mortal(alice).
    premises = [_S.parse("∀x:Human Mortal(x)")]
    assert find_countermodel(premises, _S.parse("Mortal(alice:Human)"), max_size=3) is None


def test_sorted_quantifier_ranges_only_over_its_sort():
    # ∀x:A P(x) does NOT entail ∀x:B P(x): a model with B ⊄ A and P false off A refutes it.
    cm = find_countermodel([_S.parse("∀x:A P(x)")], _S.parse("∀x:B P(x)"), max_size=2)
    assert cm is not None
    assert "A" in cm.sorts and "B" in cm.sorts


def test_sorted_validity_has_no_countermodel():
    # (∀x:Human Mortal(x)) → Mortal(alice:Human) is valid (alice is a Human).
    f = _S.parse("(∀x:Human Mortal(x)) → Mortal(alice:Human)")
    assert is_valid_finite(f, max_size=3) is True


def test_sorted_unsatisfiable_theory():
    # ∀x:Human Mortal(x) together with ¬Mortal(bob:Human) is unsatisfiable.
    theory = [_S.parse("∀x:Human Mortal(x)"), _S.parse("¬Mortal(bob:Human)")]
    assert find_model(theory, max_size=3) is None


def test_empty_sorts_fall_back_to_classical_fol():
    # A plain FOL formula (no sorts) still finds an ordinary model with empty sorts.
    m = find_model([_F.parse("P(a)")], max_size=2)
    assert m is not None and m.sorts == {}
    assert is_valid_finite(_F.parse("P(a) → P(a)")) is True
    assert is_valid_finite(_F.parse("∀x (P(x) → P(x))")) is True


def test_sorted_satisfiable_distinct_sorts():
    # Two sorts with disjoint requirements are jointly satisfiable.
    theory = [_S.parse("∀x:A P(x)"), _S.parse("∀x:B ¬P(x)"),
              _S.parse("A(ann:A)"), _S.parse("B(ben:B)")]
    assert is_satisfiable_finite(theory[0], max_size=2) is True
    m = find_model(theory, max_size=3)
    assert m is not None
