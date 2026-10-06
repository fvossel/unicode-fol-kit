"""The truth constants in the evaluators and the non-classical routes.

Every expected value is worked out by hand from the reading each logic gives the
constants:

* classical, three-valued, matrix: ``$true`` has the top value (``1`` in K3 and LP,
  ``T`` in FDE), ``$false`` the bottom value (``0`` / ``F``);
* fuzzy: the degrees ``1`` and ``0``;
* modal, graded modal, intuitionistic: the same at every world (``$true`` is forced
  everywhere, ``$false`` nowhere, whatever the valuation and the order);
* a logic with no agreed reading (relevant, linear, Lambek, the deep embeddings)
  refuses the constants by name.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Constant, Variable, Quantifier, Box, Diamond,
    LukNegation, LukImplication,
)
from unicode_fol_kit.fol.msflparser import MSFLParser

T = Atom("$true", ())
F = Atom("$false", ())
P = Atom("P", ())
Q = Atom("Q", ())


# ---------------------------------------------------------------------------
# Truth tables and the three-valued evaluator
# ---------------------------------------------------------------------------

def test_truth_table_has_no_column_for_a_constant():
    from unicode_fol_kit.semantics.truthtable import truth_table
    table = truth_table(Implies(F, P), "classical")
    assert table.atoms == ("P",)
    # ⊥ → P holds at both rows: the premise is false
    assert [row[1] for row in table.rows] == [1.0, 1.0]
    assert table.is_tautology


def test_truth_table_of_only_a_constant_has_one_row():
    from unicode_fol_kit.semantics.truthtable import truth_table
    assert truth_table(T, "classical").atoms == ()
    assert [row[1] for row in truth_table(T, "classical").rows] == [1.0]
    assert [row[1] for row in truth_table(F, "classical").rows] == [0.0]


@pytest.mark.parametrize("logic", ["K3", "LP"])
def test_three_valued_truth_tables_read_the_extremes(logic):
    from unicode_fol_kit.semantics.truthtable import truth_table
    # $true ∧ P = min(1, p) = p, and $false ∨ P = max(0, p) = p, at each of the
    # three values 0, ½, 1 of P (the table's own row order is not asserted)
    for formula in (And(T, P), Or(F, P)):
        table = truth_table(formula, logic)
        assert table.atoms == ("P",)
        assert {row[0][0]: row[1] for row in table.rows} == {0.0: 0.0, 0.5: 0.5, 1.0: 1.0}


def test_kleene_value_of_the_constants():
    from unicode_fol_kit.semantics.manyvalued import kleene_value
    assert kleene_value(T, {}) == 1.0
    assert kleene_value(F, {}) == 0.0
    assert kleene_value(Not(F), {}) == 1.0
    # ½ is the value of an undetermined letter, and min(1, ½) = ½
    assert kleene_value(And(T, P), {"P": 0.5}) == 0.5


def test_k3_validity_with_constants():
    from unicode_fol_kit.semantics.manyvalued import is_valid, entails
    # K3 designates only 1. $true is 1 and $false is 0, so:
    assert is_valid(T, "K3")
    assert not is_valid(F, "K3")
    assert is_valid(Implies(F, F), "K3")        # max(1-0, 0) = 1
    assert is_valid(Or(P, T), "K3")             # max(p, 1) = 1 at every p
    # a letter alone keeps its gap: P ∨ ¬P is ½ at p = ½, a constant does not repair it
    assert not is_valid(Or(P, Not(P)), "K3")
    # entailment: the premise $false is never designated, so it entails anything
    assert entails([F], P, "K3")


def test_lp_designates_the_half_but_not_the_bottom():
    from unicode_fol_kit.semantics.manyvalued import entails
    assert entails([], T, "LP")
    assert not entails([], F, "LP")
    assert entails([F], P, "LP")        # $false is 0, never designated, even in LP
    assert not entails([T], P, "LP")


# ---------------------------------------------------------------------------
# Logical matrices: declared top and bottom
# ---------------------------------------------------------------------------

def test_the_shipped_matrices_declare_their_extremes():
    from unicode_fol_kit.semantics.matrix import K3_MATRIX, LP_MATRIX, FDE_MATRIX
    assert (K3_MATRIX.top, K3_MATRIX.bottom) == (1.0, 0.0)
    assert (LP_MATRIX.top, LP_MATRIX.bottom) == (1.0, 0.0)
    assert (FDE_MATRIX.top, FDE_MATRIX.bottom) == ("T", "F")


def test_matrix_value_of_the_constants():
    from unicode_fol_kit.semantics.matrix import matrix_value, K3_MATRIX, FDE_MATRIX
    assert matrix_value(T, {}, K3_MATRIX) == 1.0
    assert matrix_value(F, {}, K3_MATRIX) == 0.0
    assert matrix_value(T, {}, FDE_MATRIX) == "T"
    assert matrix_value(F, {}, FDE_MATRIX) == "F"
    # in FDE, ¬T = F and ¬F = T, and T ∧ P = P at P = B
    assert matrix_value(Not(T), {}, FDE_MATRIX) == "F"
    assert matrix_value(Not(F), {}, FDE_MATRIX) == "T"
    assert matrix_value(And(T, P), {"P": "B"}, FDE_MATRIX) == "B"


def _two_valued(**kwargs):
    from unicode_fol_kit.semantics.matrix import TruthMatrix
    return TruthMatrix.from_functions(
        "two", [0, 1], [1], neg=lambda a: 1 - a, conj=min, disj=max, **kwargs)


def test_a_matrix_that_declares_no_extremes_refuses_the_constants_by_name():
    from unicode_fol_kit.semantics.matrix import matrix_value
    matrix = _two_valued()
    with pytest.raises(NotImplementedError) as info:
        matrix_value(T, {}, matrix)
    message = str(info.value)
    assert "two" in message and "$true" in message and "top" in message
    with pytest.raises(NotImplementedError) as info:
        matrix_value(F, {}, matrix)
    assert "$false" in str(info.value) and "bottom" in str(info.value)
    # a formula with no constant is unaffected
    assert matrix_value(And(P, Q), {"P": 1, "Q": 1}, matrix) == 1


def test_a_matrix_that_declares_its_extremes_reads_the_constants():
    from unicode_fol_kit.semantics.matrix import matrix_value
    matrix = _two_valued(top=1, bottom=0)
    assert matrix_value(T, {}, matrix) == 1
    assert matrix_value(Not(F), {}, matrix) == 1


def test_a_declared_extreme_must_be_a_value_of_the_matrix():
    with pytest.raises(ValueError):
        _two_valued(top=7)


# ---------------------------------------------------------------------------
# Fuzzy logic: the degrees 1 and 0
# ---------------------------------------------------------------------------

@pytest.fixture
def fl():
    return MSFLParser(fuzzy=True)


def test_fuzzy_degrees_of_the_constants(fl):
    from unicode_fol_kit.semantics.fuzzy import evaluate
    assert evaluate(fl.parse("⊤"), {}) == 1.0
    assert evaluate(fl.parse("⊥"), {}) == 0.0
    # Łukasiewicz: ¬a = 1-a, a ⊗ b = max(0, a+b-1), a ⊕ b = min(1, a+b), a → b = min(1, 1-a+b)
    p = {"P": 0.3}
    assert evaluate(fl.parse("¬⊤"), p) == pytest.approx(0.0)
    assert evaluate(fl.parse("P ⊗ ⊤"), p) == pytest.approx(0.3)        # max(0, 0.3+1-1)
    assert evaluate(fl.parse("P ⊕ ⊥"), p) == pytest.approx(0.3)        # min(1, 0.3+0)
    assert evaluate(fl.parse("⊤ → P"), p) == pytest.approx(0.3)        # min(1, 1-1+0.3)
    assert evaluate(fl.parse("P → ⊥"), p) == pytest.approx(0.7)        # min(1, 1-0.3+0)
    assert evaluate(fl.parse("⊥ → P"), p) == pytest.approx(1.0)        # min(1, 1-0+0.3) capped


def test_fuzzy_validity_by_z3(fl):
    from unicode_fol_kit.atp.z3_fuzzy import fuzzy_is_valid
    assert fuzzy_is_valid(fl.parse("⊤")) is True
    assert fuzzy_is_valid(fl.parse("⊥")) is False
    assert fuzzy_is_valid(fl.parse("⊥ → P")) is True
    assert fuzzy_is_valid(fl.parse("⊤ → P")) is False                  # p = 0 gives 0
    assert fuzzy_is_valid(fl.parse("P ⊗ ⊤ ↔ P")) is True
    assert fuzzy_is_valid(fl.parse("¬⊥")) is True


def test_fuzzy_modal_degrees_do_not_depend_on_the_world():
    from unicode_fol_kit.semantics.fuzzy_kripke import FuzzyKripkeModel, satisfies_fuzzy_modal
    # world 0 sees world 1 with weight 0.25; world 1 sees nothing
    model = FuzzyKripkeModel({0, 1}, {"alethic": {(0, 1): 0.25}})
    assert satisfies_fuzzy_modal(T, model, 0) == 1.0
    assert satisfies_fuzzy_modal(F, model, 1) == 0.0
    # Łukasiewicz: □⊥ at 0 = min over successors of (0.25 → 0) = 1 - 0.25
    assert satisfies_fuzzy_modal(Box(F), model, 0) == pytest.approx(0.75)
    # ◇⊤ at 0 = max over successors of (0.25 ⊗ 1) = 0.25
    assert satisfies_fuzzy_modal(Diamond(T), model, 0) == pytest.approx(0.25)
    # at the dead end □⊥ is vacuously 1 and ◇⊤ is 0
    assert satisfies_fuzzy_modal(Box(F), model, 1) == 1.0
    assert satisfies_fuzzy_modal(Diamond(T), model, 1) == 0.0


# ---------------------------------------------------------------------------
# Modal, intuitionistic
# ---------------------------------------------------------------------------

def test_crisp_modal_constants_hold_at_every_world():
    from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
    # 0 -> 1, and 1 is a dead end; no atom is true anywhere
    model = KripkeModel({0, 1}, {"alethic": {(0, 1)}}, {0: set(), 1: set()})
    assert satisfies_modal(T, model, 0) and satisfies_modal(T, model, 1)
    assert not satisfies_modal(F, model, 0) and not satisfies_modal(F, model, 1)
    assert not satisfies_modal(Box(F), model, 0)        # a successor exists, and ⊥ fails there
    assert satisfies_modal(Box(F), model, 1)            # no successor: vacuously true
    assert satisfies_modal(Diamond(T), model, 0)
    assert not satisfies_modal(Diamond(T), model, 1)    # ◇⊤ needs a successor
    assert not satisfies_modal(Diamond(F), model, 0)
    assert satisfies_modal(Box(T), model, 0) and satisfies_modal(Box(T), model, 1)


def test_intuitionistic_forcing_of_the_constants():
    from unicode_fol_kit.semantics.intuitionistic import IntKripkeModel
    # 0 ≤ 1, P forced from 1 on
    model = IntKripkeModel(upset={0: frozenset({0, 1}), 1: frozenset({1})},
                           valuation={"P": frozenset({1})})
    for world in (0, 1):
        assert model.forces(world, T)
        assert not model.forces(world, F)
        assert model.forces(world, Not(F))          # no later world forces $false
        assert not model.forces(world, Not(T))
        assert model.forces(world, Implies(F, P))   # nothing forces the antecedent
    assert not model.forces(0, Implies(T, P))       # $true is forced at 0 and P is not
    assert model.forces(1, Implies(T, P))


def test_intuitionistic_kripke_counter_model_for_true_implies_p():
    from unicode_fol_kit.semantics.intuitionistic import int_countermodel, int_valid
    assert int_valid(Implies(F, P))
    assert int_countermodel(Implies(F, P)) is None
    found = int_countermodel(Implies(T, P))
    assert found is not None
    model, world = found
    assert model.forces(world, T) and not model.forces(world, P)


def test_excluded_middle_stays_invalid_with_a_constant_in_it():
    from unicode_fol_kit.semantics.intuitionistic import int_valid
    assert not int_valid(Or(P, Not(P)))
    assert not int_valid(Or(Or(P, Not(P)), F))      # a false disjunct adds nothing
    assert int_valid(Or(Or(P, Not(P)), T))          # a true disjunct makes it valid


def test_goedel_translation_keeps_the_constants():
    from unicode_fol_kit.hol.intuitionistic import gmt_translate
    # T($true) = $true, T($false) = $false (textbook ⊥ ↦ ⊥), and → gets its box
    assert gmt_translate(T) == T
    assert gmt_translate(F) == F
    assert gmt_translate(Implies(F, P)) == Box(Implies(F, Box(P)))


# ---------------------------------------------------------------------------
# First-order structures, free logic
# ---------------------------------------------------------------------------

def test_tarski_satisfaction_of_the_constants():
    from unicode_fol_kit.semantics.tarski import Structure, satisfies
    structure = Structure(domain=[1], predicates={("P", 0): False})
    assert satisfies(T, structure)
    assert not satisfies(F, structure)
    assert satisfies(Not(F), structure)
    assert satisfies(Implies(F, P), structure)
    assert not satisfies(Implies(T, P), structure)


def test_free_logic_constants_hold_in_an_empty_domain():
    from unicode_fol_kit.semantics.free_logic import FreeModel, free_satisfies
    empty = FreeModel(outer=(), existing=frozenset())
    for policy in ("negative", "positive"):
        assert free_satisfies(T, empty, policy=policy)
        assert not free_satisfies(F, empty, policy=policy)
        assert free_satisfies(Not(F), empty, policy=policy)


def test_the_name_with_arguments_is_an_ordinary_predicate_in_a_structure():
    from unicode_fol_kit.semantics.tarski import Structure, satisfies
    odd = Atom("$true", [Constant("a")])
    structure = Structure(domain=[1], constants={"a": 1}, predicates={("$true", 1): set()})
    assert not satisfies(odd, structure)       # the empty relation, not the constant


# ---------------------------------------------------------------------------
# Logics with no agreed reading refuse the constants by name
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("constant", [T, F])
def test_relevant_logic_refuses_the_constants(constant):
    from unicode_fol_kit.semantics.relevant import rel_valid, rel_countermodel
    for call in (rel_valid, rel_countermodel):
        with pytest.raises(TypeError) as info:
            call(Implies(P, constant))
        message = str(info.value)
        assert constant.predicate in message
        assert "relevant" in message
        assert "additive" in message and "multiplicative" in message


@pytest.mark.parametrize("constant", [T, F])
def test_linear_logic_refuses_the_constants(constant):
    from unicode_fol_kit.atp.linear import ill_prove, ill_derivable
    for call in (ill_prove, ill_derivable):
        with pytest.raises(NotImplementedError) as info:
            call([P], constant)
        message = str(info.value)
        assert constant.predicate in message
        assert "linear" in message
    with pytest.raises(NotImplementedError):
        ill_prove([constant], P)


@pytest.mark.parametrize("constant", [T, F])
def test_the_lambek_calculus_refuses_the_constants(constant):
    from unicode_fol_kit.atp.lambek import lambek_prove, lambek_derivable
    for call in (lambek_prove, lambek_derivable):
        with pytest.raises(NotImplementedError) as info:
            call([P], constant)
        assert constant.predicate in str(info.value)
        assert "Lambek" in str(info.value)
    with pytest.raises(NotImplementedError):
        lambek_prove([constant, P], Q)


def test_the_linear_and_relevant_backends_say_unsupported_not_unknown_letters():
    from unicode_fol_kit.api import prove
    for name in ("ill", "relevant", "lambek"):
        verdict = prove(T, [P], backends=[name], logic=name)
        assert verdict.status == "unknown", name
        assert "unsupported" in str(verdict.detail), name
        assert "no agreed reading" in str(verdict.detail), name
        assert "$true" in str(verdict.detail), name


def test_a_letter_is_still_a_letter_in_the_logics_that_refuse_constants():
    from unicode_fol_kit.atp.linear import ill_derivable
    from unicode_fol_kit.atp.lambek import lambek_derivable
    assert ill_derivable([P], P)
    assert lambek_derivable([P], P)
