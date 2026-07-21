# -*- coding: utf-8 -*-
"""Isabelle export + decision for the counterfactual conditionals □→ / ◇→.

Structure tests always run. The live tests build the emitted theories in a real
Isabelle, so exit 0 certifies the verdicts against the same Lewis sphere condition
cf_satisfies evaluates; they also validate the runner differentially against a
brute-force sweep of small sphere models.
"""

import itertools

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import Atom
from unicode_fol_kit.hol.isabelle_conditional import (
    isabelle_conditional_theory, to_isabelle_conditional,
    battery_proof, nitpick_proof, DEFAULT_METHODS,
)
from unicode_fol_kit.hol.isabelle_runner import (
    isabelle_available, isabelle_decide_counterfactual,
)
from unicode_fol_kit.semantics.conditional import CounterfactualModel, cf_satisfies

_MODAL = MSFLParser(modal=True)

requires_isabelle = pytest.mark.skipif(
    not isabelle_available(), reason="no local Isabelle installation found")
isabelle_live = pytest.mark.isabelle_live


# --------------------------------------------------------------------------- #
# Structure tests (always run).
# --------------------------------------------------------------------------- #

class TestEncoder:
    def test_would_becomes_the_sphere_conditional(self):
        assert to_isabelle_conditional(_MODAL.parse("A □→ B")) == \
            "(CondC p_A p_B)"

    def test_might_desugars_to_the_dual(self):
        # ◇→ gets no constant of its own, so the emitted theory cannot drift from
        # the evaluator's derivation ¬(A □→ ¬B).
        assert to_isabelle_conditional(_MODAL.parse("A ◇→ B")) == \
            "(NegC (CondC p_A (NegC p_B)))"

    def test_propositional_connectives_encode(self):
        assert to_isabelle_conditional(_MODAL.parse("(A ∧ B) □→ (A ∨ ¬B)")) == \
            "(CondC (AndC p_A p_B) (OrC p_A (NegC p_B)))"

    def test_modal_operators_are_rejected(self):
        # □/◇ range over an accessibility relation, not a similarity ordering —
        # the boundary cf_satisfies enforces, mirrored at export time.
        for src in ["□A □→ B", "A □→ ◇B"]:
            with pytest.raises(NotImplementedError, match="isabelle_modal"):
                to_isabelle_conditional(_MODAL.parse(src))

    def test_quantifiers_are_rejected(self):
        fol = MSFLParser()
        with pytest.raises(NotImplementedError, match="propositional"):
            to_isabelle_conditional(fol.parse("∀x P(x)"))


class TestTheory:
    def test_nesting_is_a_premise_not_an_axiom(self):
        # nitpick cannot certify a countermodel as GENUINE while axiomatised
        # constants are in play (it downgrades to quasi_genuine), so the theory
        # must state nesting as a premise of the goal and axiomatise nothing.
        thy = isabelle_conditional_theory(_MODAL.parse("A □→ A"))
        assert "axiomatization" not in thy
        assert 'lemma goal: "nested Sel \\<Longrightarrow>' in thy

    def test_battery_is_verit_first(self):
        # The | combinator has no per-method timeout and blast does not terminate
        # on agglomeration, so a blast-first battery would hang before reaching
        # verit. Pin the order.
        assert DEFAULT_METHODS[0] == "smt (verit)"
        assert battery_proof().splitlines()[-1].lstrip().startswith(
            "by (smt (verit)")

    def test_nitpick_theory_targets_the_world_type(self):
        thy = isabelle_conditional_theory(
            _MODAL.parse("A □→ B"), proof=nitpick_proof(card="1-3"))
        assert "nitpick[card w = 1-3" in thy and "expect = genuine" in thy

    def test_illegal_theory_name_rejected(self):
        with pytest.raises(ValueError):
            isabelle_conditional_theory(_MODAL.parse("A □→ A"), theory_name="1bad")


# --------------------------------------------------------------------------- #
# Live tests (need a local Isabelle).
# --------------------------------------------------------------------------- #

#: Hand-checked Lewis facts: the headline validities and the two classical laws
#: whose FAILURE is the point of the counterfactual.
_LEWIS_FACTS = [
    ("A □→ A", True),                                       # identity
    ("((A □→ B) ∧ (A □→ C)) → (A □→ (B ∧ C))", True),       # agglomeration
    ("(A □→ B) → (A □→ (B ∨ C))", True),                    # weakened consequent
    ("(A ◇→ B) → ¬(A □→ ¬B)", True),                        # duality
    ("(A □→ B) → ((A ∧ C) □→ B)", False),                   # antecedent strengthening
    ("(A □→ B) → (¬B □→ ¬A)", False),                       # contraposition
]


@isabelle_live
@requires_isabelle
@pytest.mark.parametrize("src,expected_valid", _LEWIS_FACTS)
def test_isabelle_certifies_the_lewis_facts(src, expected_valid):
    verdict = isabelle_decide_counterfactual(_MODAL.parse(src))
    assert verdict.status == ("valid" if expected_valid else "invalid"), \
        f"{src}: {verdict}"


@isabelle_live
@requires_isabelle
def test_invalid_verdicts_agree_with_the_python_evaluator():
    # Differential check: for each formula Isabelle refutes, a brute-force sweep
    # of small sphere models must also find a countermodel — the two ends of the
    # toolkit implement one truth condition.
    A, B, C = (Atom(n, ()) for n in "ABC")
    worlds = (0, 1, 2)
    sphere_choices = [
        [frozenset({0}), frozenset({0, 1}), frozenset({0, 1, 2})],
        [frozenset({0, 1}), frozenset({0, 1, 2})],
        [frozenset({0, 1, 2})],
    ]
    for src, expected_valid in _LEWIS_FACTS:
        if expected_valid:
            continue
        f = _MODAL.parse(src)
        refuted = False
        for bits in itertools.product([frozenset(), frozenset({"A"}),
                                       frozenset({"A", "B"}),
                                       frozenset({"A", "C"}),
                                       frozenset({"B"}), frozenset({"C"})],
                                      repeat=3):
            val = dict(zip(worlds, bits))
            for spheres in sphere_choices:
                model = CounterfactualModel(worlds, val, {w: spheres for w in worlds})
                if any(not cf_satisfies(f, model, w) for w in worlds):
                    refuted = True
                    break
            if refuted:
                break
        assert refuted, f"python evaluator found no countermodel for {src}"
