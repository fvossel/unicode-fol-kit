"""Tests for truth tables, FOL→NL, the finite model finder, tableaux, and intuitionistic logic.

Each subsystem is cross-checked against an independent oracle: truth tables and
tableaux against Z3 (classical), the model finder against Z3 validity, intuitionistic
validity against classical validity (the soundness inclusion int ⊆ classical).
"""

from functools import reduce
import random

import pytest

from unicode_fol_kit import MSFLParser, is_valid, is_satisfiable
from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Xor, Quantifier, Variable, Constant,
)
from unicode_fol_kit import (
    truth_table, is_tautology, is_contradiction, is_satisfiable_tt,
    find_model, find_countermodel, is_satisfiable_finite, is_valid_finite,
    is_valid_tableau, prove_tableau, tableau_model, tableau_closed,
    int_valid, int_countermodel, to_english,
)
from unicode_fol_kit.semantics.tarski import models
from unicode_fol_kit.semantics.modelfinder import _universal_closure

_P = MSFLParser()
P, Q, R, S = (Atom(n, ()) for n in "PQRS")


def _rand_prop(rng, depth, atoms):
    if depth <= 0 or rng.random() < 0.42:
        a = rng.choice(atoms)
        return Not(a) if rng.random() < 0.3 else a
    op = rng.choice([And, Or, Implies, Iff, Xor, "not"])
    if op == "not":
        return Not(_rand_prop(rng, depth - 1, atoms))
    return op(_rand_prop(rng, depth - 1, atoms), _rand_prop(rng, depth - 1, atoms))


# ---------------------------------------------------------------------------
# Truth tables
# ---------------------------------------------------------------------------

def test_truth_table_shape_and_render():
    tt = truth_table(Implies(P, Q))
    assert tt.atoms == ("P", "Q")
    assert len(tt.rows) == 4
    assert "P → Q" in tt.render() and "| T | F | F |" in tt.render()


def test_truth_table_logic_distinctions():
    lem = Or(P, Not(P))
    assert is_tautology(lem, "classical") is True
    assert is_tautology(lem, "K3") is False        # K3 has no tautologies
    assert is_tautology(lem, "LP") is True         # LEM holds in LP
    assert is_contradiction(And(P, Not(P)), "classical") is True


def test_truth_table_rejects_quantifier():
    with pytest.raises(ValueError):
        truth_table(Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])))


def test_truth_table_matches_z3():
    rng = random.Random(101)
    atoms = [P, Q, R, S]
    for _ in range(700):
        f = _rand_prop(rng, rng.randint(1, 3), atoms)
        assert is_tautology(f) == is_valid(f)
        assert is_satisfiable_tt(f) == is_satisfiable(f)


# ---------------------------------------------------------------------------
# FOL → natural language
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("formula,english", [
    ("∀x (Human(x) → Mortal(x))", "for every x, if x is human, then x is mortal"),
    ("∃x (Human(x) ∧ ¬Mortal(x))", "for some x, x is human and x is not mortal"),
    ("¬Human(socrates)", "socrates is not human"),
    ("P → (Q ∨ R)", "if P, then (Q or R)"),
])
def test_to_english(formula, english):
    assert to_english(_P.parse(formula)) == english


# ---------------------------------------------------------------------------
# Finite model finder
# ---------------------------------------------------------------------------

def test_find_model_satisfies_theory():
    theory = [_P.parse("∀x (P(x) → Q(x))"), _P.parse("P(tom)"), _P.parse("¬Q(sue)")]
    model = find_model(theory, max_size=3)
    assert model is not None
    assert all(models(_universal_closure(f), model) for f in theory)


def test_find_countermodel_for_invalid_entailment():
    cm = find_countermodel([_P.parse("P(tom)")], _P.parse("∀x P(x)"), max_size=3)
    assert cm is not None


def test_no_countermodel_for_valid_entailment():
    assert find_countermodel([_P.parse("∀x P(x)")], _P.parse("P(tom)"), max_size=4) is None


@pytest.mark.parametrize("formula", [
    "P(tom) → P(tom)", "∀x P(x) → P(tom)", "P(tom) → ∃x P(x)",
    "∀x (P(x) → Q(x)) → (P(tom) → Q(tom))", "∃x ∀y R(x, y) → ∀y ∃x R(x, y)",
])
def test_valid_has_no_finite_countermodel(formula):
    f = _P.parse(formula)
    assert is_valid(f)               # Z3 says valid
    assert is_valid_finite(f, max_size=3)   # so no finite countermodel exists


def test_invalid_has_finite_countermodel():
    for formula in ["∃x P(x) → ∀x P(x)", "P(tom) → Q(tom)"]:
        assert not is_valid_finite(_P.parse(formula), max_size=3)


# ---------------------------------------------------------------------------
# Tableaux
# ---------------------------------------------------------------------------

def test_tableau_matches_z3_propositional():
    rng = random.Random(202)
    atoms = [P, Q, R, S]
    for _ in range(800):
        f = _rand_prop(rng, rng.randint(1, 3), atoms)
        assert is_valid_tableau(f) == is_valid(f)
        assert (tableau_model([f]) is not None) == is_satisfiable(f)


def test_tableau_countermodel():
    assert tableau_model([_P.parse("P → Q"), _P.parse("P"), _P.parse("¬Q")]) is None
    model = tableau_model([_P.parse("P → Q"), _P.parse("P")])
    assert model == {"P": True, "Q": True}


@pytest.mark.parametrize("premises,goal,entailed", [
    (["∀x (P(x) → Q(x))", "P(tom)"], "Q(tom)", True),
    ([], "∀x P(x) → P(tom)", True),
    ([], "∃x ∀y R(x, y) → ∀y ∃x R(x, y)", True),
    ([], "∀y ∃x R(x, y) → ∃x ∀y R(x, y)", False),
    ([], "∃x P(x) → ∀x P(x)", False),
])
def test_tableau_fol(premises, goal, entailed):
    prems = [_P.parse(p) for p in premises]
    if entailed:
        assert prove_tableau(prems, _P.parse(goal))
    else:
        assert not prove_tableau(prems, _P.parse(goal))


# ---------------------------------------------------------------------------
# Intuitionistic logic
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("formula,valid", [
    ("P ∨ ¬P", False),              # LEM fails
    ("¬¬P → P", False),             # double-negation elimination fails
    ("((P → Q) → P) → P", False),   # Peirce fails
    ("P → ¬¬P", True),
    ("¬¬(P ∨ ¬P)", True),           # double-negated LEM holds
    ("¬(P ∧ ¬P)", True),
    ("P → (Q → P)", True),
])
def test_intuitionistic_headline_facts(formula, valid):
    f = _P.parse(formula)
    assert int_valid(f, max_worlds=3) is valid
    if not valid:
        assert int_countermodel(f, max_worlds=3) is not None


def test_intuitionistic_subset_of_classical():
    rng = random.Random(303)
    atoms = [P, Q, R]
    found = 0
    for _ in range(500):
        f = _rand_prop(rng, rng.randint(1, 3), atoms)
        if int_valid(f, max_worlds=3):
            assert is_valid(f), f"int-valid but not classically valid: {f.to_unicode_str()}"
            found += 1
    assert found > 0


# ---------------------------------------------------------------------------
# Exports
# ---------------------------------------------------------------------------

def test_exports():
    import unicode_fol_kit as u
    for name in ("truth_table", "TruthTable", "is_tautology", "is_contradiction",
                 "is_satisfiable_tt", "find_model", "find_countermodel",
                 "is_satisfiable_finite", "is_valid_finite", "is_valid_tableau",
                 "prove_tableau", "tableau_model", "tableau_closed",
                 "int_valid", "int_countermodel", "IntKripkeModel", "to_english"):
        assert hasattr(u, name) and name in u.__all__, name
