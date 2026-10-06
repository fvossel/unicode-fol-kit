"""The proof calculi and their checkers know the two truth constants.

Each calculus has its own way to say it:

* sequent calculus: ``Γ ⊢ Δ, $true`` and ``Γ, $false ⊢ Δ`` are axioms;
* intuitionistic sequent calculus: the same two axioms, with one succedent formula;
* Fitch: introduction of ``$true`` from nothing, elimination of ``$false``;
* tableau: a branch holding ``$false`` or ``¬$true`` is closed, and no other single
  literal closes one;
* resolution: a clause with ``$true`` (or ``¬$false``) is true and is dropped, a
  ``$false`` (or ``¬$true``) literal is false and is removed.

A checker accepts exactly those steps and rejects every other use of the constants,
in particular ``$true`` as an axiom for another atom.
"""

from itertools import product

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Constant, Variable,
)
from unicode_fol_kit.atp.sequent import (
    sequent, derive, axiom, check_sequent_proof, verify_sequent_proof,
)
from unicode_fol_kit.atp.lj import check_lj_proof, verify_lj_proof
from unicode_fol_kit.atp.fitch import (
    Proof, Subproof, premise, assume, line, FALSUM, verify_proof, check_proof,
)
from unicode_fol_kit.atp.tableau import (
    prove_tableau_detailed, TableauProof, TableauClosure,
)
from unicode_fol_kit.atp.tableau_check import check_tableau_proof, TableauCheckError
from unicode_fol_kit.atp.resolution import to_clauses, prove as resolution_prove
from unicode_fol_kit.atp.resolution_check import (
    ResolutionStep, ResolutionDerivation, verify_resolution_proof,
)

T = Atom("$true", ())
F = Atom("$false", ())
P = Atom("P", ())
Q = Atom("Q", ())


# ---------------------------------------------------------------------------
# Sequent calculus: the axiom rule accepts exactly the valid sequents of atoms
# ---------------------------------------------------------------------------

ATOMS = (P, T, F)


def _subsets(items):
    out = [()]
    for item in items:
        out += [s + (item,) for s in out]
    return out


def _holds(sequent_, p_value):
    """Whether ``⋀antecedent → ⋁succedent`` holds when ``P`` has ``p_value``."""
    def value(atom):
        return {"P": p_value, "$true": True, "$false": False}[atom.predicate]
    return (not all(value(a) for a in sequent_.antecedent)
            or any(value(a) for a in sequent_.succedent))


def _valid(sequent_):
    return all(_holds(sequent_, p_value) for p_value in (False, True))


ALL_SEQUENTS = [sequent(list(a), list(s))
                for a, s in product(_subsets(ATOMS), _subsets(ATOMS))]


def test_sequent_axiom_accepts_exactly_the_valid_sequents_over_the_atoms():
    # 64 sequents with each side a subset of {P, $true, $false}. Worked by hand
    # for the two sides: P on both sides is the identity axiom, $true on the right
    # and $false on the left are the constant axioms; every other sequent has a
    # countermodel (P true when P is only on the left, false when it is only on
    # the right), so it is invalid and no axiom.
    assert len(ALL_SEQUENTS) == 64
    for s in ALL_SEQUENTS:
        assert check_sequent_proof(axiom(s)) == _valid(s), s


def test_sequent_axiom_accepts_the_named_forms():
    assert check_sequent_proof(axiom(sequent([], [T])))
    assert check_sequent_proof(axiom(sequent([P], [Q, T])))
    assert check_sequent_proof(axiom(sequent([F], [P])))
    assert check_sequent_proof(axiom(sequent([P, F], [])))


def test_sequent_axiom_rejects_the_converse_forms():
    assert not check_sequent_proof(axiom(sequent([T], [P])))     # $true on the left
    assert not check_sequent_proof(axiom(sequent([], [F])))      # $false on the right
    assert not check_sequent_proof(axiom(sequent([T], [])))
    assert not check_sequent_proof(axiom(sequent([P], [F])))


def test_sequent_true_axiom_is_not_an_axiom_for_another_atom():
    tampered = axiom(sequent([], [P]))
    result = verify_sequent_proof(tampered)
    assert not result.ok
    assert "$true" in result.error and "$false" in result.error


def test_sequent_constant_with_an_argument_is_no_constant():
    # `$true(a)` is an ordinary predicate that is spelled like the constant
    odd = Atom("$true", [Constant("a")])
    assert not check_sequent_proof(axiom(sequent([], [odd])))
    assert not check_sequent_proof(axiom(sequent([Atom("$false", [Constant("a")])], [P])))


def test_sequent_derivations_through_the_constant_axioms():
    # ⊢ ¬$false:  ¬R from the axiom `$false ⊢`
    not_false = derive(sequent([], [Not(F)]), "¬R", axiom(sequent([F], [])))
    assert check_sequent_proof(not_false)
    # P ⊢ $true ∧ P:  ∧R from `P ⊢ $true` and `P ⊢ P`
    conj = derive(sequent([P], [And(T, P)]), "∧R",
                  axiom(sequent([P], [T])), axiom(sequent([P], [P])))
    assert check_sequent_proof(conj)
    # $false ⊢ P:  the axiom itself
    assert check_sequent_proof(axiom(sequent([F], [P])))


def test_sequent_derivation_with_a_tampered_leaf_is_rejected():
    # the same ∧R, but the left leaf `P ⊢ $false` is no axiom ($false on the right)
    bad = derive(sequent([P], [And(F, P)]), "∧R",
                 axiom(sequent([P], [F])), axiom(sequent([P], [P])))
    assert not check_sequent_proof(bad)


# ---------------------------------------------------------------------------
# Intuitionistic sequent calculus (LJ)
# ---------------------------------------------------------------------------

LJ_SEQUENTS = [sequent(list(a), list(s))
               for a, s in product(_subsets(ATOMS), [(), (P,), (T,), (F,)])]


def test_lj_axiom_accepts_exactly_the_valid_single_succedent_sequents():
    for s in LJ_SEQUENTS:
        assert check_lj_proof(axiom(s)) == _valid(s), s


def test_lj_derivations_through_the_constant_axioms():
    assert check_lj_proof(axiom(sequent([], [T])))
    assert check_lj_proof(axiom(sequent([F], [P])))
    assert check_lj_proof(derive(sequent([], [Not(F)]), "¬R", axiom(sequent([F], []))))


def test_lj_rejects_true_as_an_axiom_for_another_atom():
    result = verify_lj_proof(axiom(sequent([], [P])))
    assert not result.ok
    assert not check_lj_proof(axiom(sequent([T], [P])))
    assert not check_lj_proof(axiom(sequent([], [F])))


# ---------------------------------------------------------------------------
# Fitch: introduction of $true, elimination of $false
# ---------------------------------------------------------------------------

def test_fitch_true_introduction_from_nothing():
    proof = Proof(steps=[line(1, T, "⊤I")])
    assert check_proof(proof)


def test_fitch_true_introduction_proves_a_conjunction_with_a_premise():
    # P ⊢ $true ∧ P
    proof = Proof(premises=[premise(1, P)],
                  steps=[line(2, T, "⊤I"), line(3, And(T, P), "∧I", 2, 1)])
    result = verify_proof(proof)
    assert result.ok, result.error


def test_fitch_true_introduction_only_concludes_the_true_constant():
    for wrong in (P, F, Not(T)):
        result = verify_proof(Proof(steps=[line(1, wrong, "⊤I")]))
        assert not result.ok, wrong
        assert "⊤I" in result.error


def test_fitch_true_introduction_cites_nothing():
    proof = Proof(premises=[premise(1, P)], steps=[line(2, T, "⊤I", 1)])
    assert not check_proof(proof)


def test_fitch_false_elimination_yields_anything():
    # $false ⊢ P  (⊥E from the constant)
    proof = Proof(premises=[premise(1, F)], steps=[line(2, P, "⊥E", 1)])
    result = verify_proof(proof)
    assert result.ok, result.error


def test_fitch_false_elimination_needs_a_falsum_line():
    for not_falsum in (P, T):
        proof = Proof(premises=[premise(1, not_falsum)], steps=[line(2, Q, "⊥E", 1)])
        assert not check_proof(proof), not_falsum


def test_fitch_the_reserved_falsum_and_the_constant_are_one_falsum():
    # ⊥I into the constant, then ⊥E out of it: ¬$true ⊢ P
    proof = Proof(premises=[premise(1, Not(T))],
                  steps=[line(2, T, "⊤I"),
                         line(3, F, "⊥I", 2, 1),
                         line(4, P, "⊥E", 3)])
    result = verify_proof(proof)
    assert result.ok, result.error
    # and the reserved atom still works the same way
    proof = Proof(premises=[premise(1, FALSUM)], steps=[line(2, P, "⊥E", 1)])
    assert check_proof(proof)


def test_fitch_negation_of_false_by_discharging_into_the_constant():
    # ⊢ ¬$false: assume $false, repeat it, discharge with ¬I
    proof = Proof(steps=[
        Subproof(assumption=assume(1, F), body=[line(2, F, "Reit", 1)]),
        line(3, Not(F), "¬I", (1, 2)),
    ])
    result = verify_proof(proof)
    assert result.ok, result.error


@pytest.mark.parametrize("logic", ["K3", "LP", "S5"])
def test_fitch_semantic_regimes_certify_the_constants(logic):
    # `$true` follows from nothing in the three-valued logics and in S5
    assert check_proof(Proof(steps=[line(1, T, "⊤I")], logic=logic))
    # `P` does not follow from nothing, whatever the rule says
    assert not check_proof(Proof(steps=[line(1, P, "⊤I")], logic=logic))
    # `$false ⊢ P`: nothing designates the premise, so the line follows
    proof = Proof(premises=[premise(1, F)], steps=[line(2, P, "⊥E", 1)], logic=logic)
    assert check_proof(proof)


# ---------------------------------------------------------------------------
# Tableau: $false and ¬$true close a branch, nothing else closes alone
# ---------------------------------------------------------------------------

def test_tableau_proves_true_and_the_checker_accepts():
    # root = [¬$true]; the literal ¬$true closes the branch on its own
    proof = prove_tableau_detailed([], T)
    assert proof is not None
    check_tableau_proof(proof, [], T)
    assert len(proof.steps) == 0
    assert [c.literal for c in proof.closures] == [Not(T)]
    assert proof.closures[0].complement is None


def test_tableau_proves_anything_from_false_and_the_checker_accepts():
    # root = [$false, ¬P]; $false closes the branch on its own
    proof = prove_tableau_detailed([F], P)
    assert proof is not None
    check_tableau_proof(proof, [F], P)
    assert F in [c.literal for c in proof.closures]


def test_tableau_does_not_prove_false():
    # root = [¬$false]: it holds in every interpretation, so it closes nothing
    assert prove_tableau_detailed([], F) is None


def test_tableau_does_not_prove_p_from_true():
    assert prove_tableau_detailed([T], P) is None


def test_tableau_checker_rejects_true_closing_alone():
    # root = [$true, ¬$true] (premise $true, conclusion $true): ¬$true closes the
    # branch by itself; citing `$true` alone is not a closure
    root = (T, Not(T))
    honest = TableauProof(root, (), (TableauClosure(0, Not(T), 0),))
    check_tableau_proof(honest, [T], T)
    tampered = TableauProof(root, (), (TableauClosure(0, T, 0),))
    with pytest.raises(TableauCheckError):
        check_tableau_proof(tampered, [T], T)


def test_tableau_checker_rejects_not_false_closing_alone():
    # root = [¬$false] (conclusion $false): ¬$false holds everywhere
    tampered = TableauProof((Not(F),), (), (TableauClosure(0, Not(F), 0),))
    with pytest.raises(TableauCheckError):
        check_tableau_proof(tampered, [], F)


def test_tableau_checker_accepts_false_and_not_true_alone():
    check_tableau_proof(TableauProof((F, Not(P)), (), (TableauClosure(0, F, 0),)), [F], P)
    check_tableau_proof(TableauProof((Not(T),), (), (TableauClosure(0, Not(T), 0),)), [], T)


# ---------------------------------------------------------------------------
# Resolution: clausification and the checker's rule
# ---------------------------------------------------------------------------

def test_clausification_drops_true_and_removes_false():
    # P ∨ $false  ->  {P}
    assert to_clauses(Or(P, F)) == {frozenset({P})}
    # P ∨ $true is true: no clause
    assert to_clauses(Or(P, T)) == set()
    # ¬$false is true: no clause
    assert to_clauses(Not(F)) == set()
    # $false is the empty clause, and so is ¬$true
    assert to_clauses(F) == {frozenset()}
    assert to_clauses(Not(T)) == {frozenset()}
    # $true ∧ P  ->  the one clause {P}
    assert to_clauses(And(T, P)) == {frozenset({P})}
    # ¬P ∨ ¬$true  ->  {¬P}
    assert to_clauses(Or(Not(P), Not(T))) == {frozenset({Not(P)})}


def test_resolution_proves_with_the_constants():
    assert resolution_prove([F], P)
    assert resolution_prove([], T)
    assert resolution_prove([], Not(F))
    assert resolution_prove([P], And(T, P))
    assert not resolution_prove([], F)
    assert not resolution_prove([T], P)


def _derivation(inputs, *steps):
    return ResolutionDerivation(inputs=inputs, steps=steps)


def test_resolution_checker_accepts_removing_false_and_not_true():
    # {P, $false} -> {P}
    d = _derivation([{P, F}],
                    ResolutionStep(1, {P, F}, "input"),
                    ResolutionStep(2, {P}, "truth_constants", (1,)))
    assert verify_resolution_proof(d).ok
    # {P, ¬$true} -> {P}
    d = _derivation([{P, Not(T)}],
                    ResolutionStep(1, {P, Not(T)}, "input"),
                    ResolutionStep(2, {P}, "truth_constants", (1,)))
    assert verify_resolution_proof(d).ok


def test_resolution_checker_derives_the_empty_clause_from_false():
    d = _derivation([{F}],
                    ResolutionStep(1, {F}, "input"),
                    ResolutionStep(2, set(), "truth_constants", (1,)))
    result = verify_resolution_proof(d)
    assert result.ok and result.refuted


def test_resolution_checker_rejects_removing_an_ordinary_literal():
    d = _derivation([{P, Q}],
                    ResolutionStep(1, {P, Q}, "input"),
                    ResolutionStep(2, {P}, "truth_constants", (1,)))
    result = verify_resolution_proof(d)
    assert not result.ok
    assert "Q" in result.error


def test_resolution_checker_rejects_removing_true_or_not_false():
    # a literal that holds in every interpretation may not be dropped as if false
    for literal in (T, Not(F)):
        d = _derivation([{P, literal}],
                        ResolutionStep(1, {P, literal}, "input"),
                        ResolutionStep(2, {P}, "truth_constants", (1,)))
        assert not verify_resolution_proof(d).ok, literal


def test_resolution_checker_rejects_a_clause_that_is_not_a_subset():
    d = _derivation([{P, F}],
                    ResolutionStep(1, {P, F}, "input"),
                    ResolutionStep(2, {Q}, "truth_constants", (1,)))
    result = verify_resolution_proof(d)
    assert not result.ok
    assert "subset" in result.error


def test_resolution_checker_rejects_a_constant_with_an_argument():
    odd = Atom("$false", [Constant("a")])
    d = _derivation([{P, odd}],
                    ResolutionStep(1, {P, odd}, "input"),
                    ResolutionStep(2, {P}, "truth_constants", (1,)))
    assert not verify_resolution_proof(d).ok


def test_resolution_checker_rule_takes_exactly_one_parent():
    d = _derivation([{P, F}],
                    ResolutionStep(1, {P, F}, "input"),
                    ResolutionStep(2, {P}, "truth_constants", (1, 1)))
    assert not verify_resolution_proof(d).ok
