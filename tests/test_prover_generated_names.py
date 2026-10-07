"""The tableau's witnesses and resolution's Skolem symbols are fresh against the whole problem.

A name the prover mints stands for an element nothing else is known about. If it has the
spelling of a symbol some formula of the problem already uses, the witness IS that symbol and
the prover proves what nobody asked. Every expectation is derived by hand:

* ``∃x P(x) ⊢ P(c)`` is NOT valid whatever ``c`` is called: universe ``{0, 1}``, ``P`` = ``{0}``,
  ``c`` ↦ 1.
* ``∃x P(x), ¬P(c) ⊢ Z(zz)`` is NOT valid: universe ``{0, 1}``, ``P`` = ``{0}``, ``c`` ↦ 1,
  ``Z`` empty makes both premises true and the conclusion false.
* ``∃x P(x) ⊢ ∃y P(y)`` is valid, and stays provable: the witness only has to be fresh.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import resolution, tableau
from unicode_logic_kit.atp.tableau import TableauClosure, TableauProof, TableauStep
from unicode_logic_kit.atp.tableau_check import (
    TableauCheckError, check_entailment_tableau_detailed, check_tableau_proof,
)
from unicode_logic_kit.fol._identifiers import symbol_names
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Function, Implies, Not, Quantifier, SortedConstant, SortedQuantifier,
    Variable,
)
from unicode_logic_kit.semantics import modelfinder
from unicode_logic_kit.semantics.tarski import satisfies

x, y = Variable("x"), Variable("y")
GENERATED = {"tableau": "_t0", "resolution": "_sk0"}


def P(term):
    return Atom("P", [term])


def Z(term):
    return Atom("Z", [term])


def exists(var, body):
    return Quantifier("∃", var, body)


def prove(backend, conclusion, premises):
    return api.prove(conclusion, premises, backends=[backend], timeout=8000)


# --------------------------------------------------------------------------- #
# a user constant spelled like a name the prover would mint
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("backend", ["tableau", "resolution"])
@pytest.mark.parametrize("spelling", ["_t0", "_sk0", "_t1", "_sk1", "_r0", "_p0"])
def test_an_existential_witness_is_not_a_user_constant(backend, spelling):
    c = Constant(spelling)
    premises = [exists(x, P(x)), Not(P(c))]
    assert prove(backend, Z(Constant("zz")), premises).status != "proved"
    assert prove(backend, P(c), [exists(x, P(x))]).status != "proved"


def test_the_two_countermodels_are_real():
    # the structure of the module docstring, written out and evaluated
    for spelling in ("_t0", "_sk0"):
        c = Constant(spelling)
        zz = Constant("zz")
        premises = [exists(x, P(x)), Not(P(c))]
        structure = modelfinder.find_countermodel(premises, Z(zz))
        assert structure is not None
        assert all(satisfies(p, structure) for p in premises)
        assert not satisfies(Z(zz), structure)
        structure = modelfinder.find_countermodel([exists(x, P(x))], P(c))
        assert structure is not None and not satisfies(P(c), structure)


@pytest.mark.parametrize("backend", ["tableau", "resolution"])
def test_a_valid_problem_with_such_constants_is_still_proved(backend):
    # ∃x P(x), Z(c) ⊢ ∃y P(y) and ⊢ Z(c) are valid whatever c is called: the witness only has
    # to be fresh, the clash must not cost the proof
    c = Constant(GENERATED[backend])
    premises = [exists(x, P(x)), Z(c)]
    assert prove(backend, exists(y, P(y)), premises).status == "proved"
    assert prove(backend, Z(c), premises).status == "proved"


@pytest.mark.parametrize("backend", ["tableau", "resolution"])
def test_the_clash_may_be_a_function_a_predicate_or_a_sorted_constant(backend):
    name = GENERATED[backend]
    # a zero-argument function and a proposition of that name are names too
    function = Function(name, [])
    assert prove(backend, Z(Constant("zz")),
                 [exists(x, P(x)), Not(P(function))]).status != "proved"
    proposition = Atom(name, [])
    assert prove(backend, And(proposition, Z(Constant("zz"))),
                 [exists(x, P(x)), proposition]).status != "proved"
    # a sorted constant (the many-sorted twin of the problem): ∃x:S P(x) ⊢ P(c:S) is not
    # valid, universe {0, 1}, S = {0, 1}, P = {0}, c ↦ 1
    sorted_c = SortedConstant(name, "S")
    assert prove(backend, P(sorted_c),
                 [SortedQuantifier("∃", x, "S", P(x))]).status != "proved"


def test_resolution_clauses_skolem_symbols_avoid_the_names_it_is_given():
    formula = exists(x, P(x))
    clauses = resolution.to_clauses(formula, avoid={"_sk0", "_sk1"})
    (clause,) = clauses
    (literal,) = clause
    skolem = literal.args[0]
    assert isinstance(skolem, Constant)
    assert skolem.name not in {"_sk0", "_sk1"}


def test_resolution_clauses_skolem_function_avoids_a_function_of_the_formula():
    # ∀y ∃x R(y, x) ∧ S(_sk0(a)): the Skolem symbol is a function of y; _sk0 is taken
    y_, x_ = Variable("y"), Variable("x")
    taken = Function("_sk0", [Constant("a0")])
    formula = And(Quantifier("∀", y_, exists(x_, Atom("R", [y_, x_]))), Atom("S", [taken]))
    clauses = resolution.to_clauses(formula)
    names = set()
    for clause in clauses:
        for literal in clause:
            names |= {n.name for n in literal.walk() if isinstance(n, Function)}
    skolem = names - {"_sk0"}
    assert len(skolem) == 1                      # the one function introduced
    assert "_sk0" in names                       # and the user's function is still there


def test_the_names_a_problem_carries_do_not_change_when_nothing_clashes():
    # no clash: the first witness is still the first generated name
    proof = tableau.prove_tableau_detailed([exists(x, P(x))], exists(y, P(y)))
    witnesses = [s.fresh_constant for s in proof.steps if s.rule == "delta"]
    assert witnesses and witnesses[0] == Constant("_t0")


# --------------------------------------------------------------------------- #
# the proof object names its generated symbols; the checker accepts the fresh names
# --------------------------------------------------------------------------- #

def test_a_proof_names_witnesses_that_the_problem_does_not_carry():
    premises = [exists(x, P(x)), Z(Constant("_t0")), Atom("_t1", [Constant("k")])]
    conclusion = exists(y, P(y))
    proof = tableau.prove_tableau_detailed(premises, conclusion)
    assert proof is not None
    taken = symbol_names(*premises, conclusion)
    witnesses = [s.fresh_constant for s in proof.steps if s.rule == "delta"]
    assert witnesses
    for witness in witnesses:
        assert witness.name not in taken
    check_tableau_proof(proof, premises, conclusion)     # and the checker certifies it
    result = check_entailment_tableau_detailed(premises, conclusion)
    assert result["proved"] and result["check_passed"] is True


def _reused_witness_proof(root_premises, conclusion, witness):
    """The 'proof' a prover that reuses a name would build for ∃x P(x), ¬P(witness) ⊢ conclusion.

    Step 1 instantiates ∃x P(x) with the constant ``witness`` as if it were fresh and the
    branch closes on ``P(witness)`` against the premise ``¬P(witness)``.
    """
    roots = tuple(root_premises) + (Not(conclusion),)
    step = TableauStep(1, 0, "delta", roots[0], (P(witness),), fresh_constant=witness)
    closure = TableauClosure(1, P(witness), 1, Not(P(witness)), 0)    # the premise is root formula 0
    return TableauProof(roots, (step,), (closure,))


def test_the_checker_rejects_a_witness_that_the_problem_already_uses():
    # the derivation of the unsound "proof" of ∃x P(x), ¬P(c) ⊢ Z(zz), in which the
    # witness of ∃x P(x) is the user's constant c
    for spelling in ("_t0", "_sk0", "kk"):
        c = Constant(spelling)
        premises = [exists(x, P(x)), Not(P(c))]
        conclusion = Z(Constant("zz"))
        proof = _reused_witness_proof(premises, conclusion, c)
        with pytest.raises(TableauCheckError, match="not fresh"):
            check_tableau_proof(proof, premises, conclusion)


def test_the_checker_rejects_a_witness_reused_from_an_earlier_step_of_the_branch():
    # ∃x P(x), ∃y Q(y), ¬∃z (P(z) ∧ Q(z)) is satisfiable (P = {0}, Q = {1}); the second
    # existential reuses the witness of the first, which would close the branch
    z_ = Variable("z")
    premises = [exists(x, P(x)), exists(y, Atom("Q", [y]))]
    conclusion = exists(z_, And(P(z_), Atom("Q", [z_])))
    c = Constant("_t0")
    roots = tuple(premises) + (Not(conclusion),)
    conj = And(P(c), Atom("Q", [c]))
    steps = (
        TableauStep(1, 0, "delta", premises[0], (P(c),), fresh_constant=c),
        TableauStep(2, 1, "delta", premises[1], (Atom("Q", [c]),), fresh_constant=c),
        TableauStep(3, 2, "gamma", roots[2], (Not(conj),), terms=(c,)),
        TableauStep(4, 3, "beta", Not(conj), (Not(P(c)),), branch_split=True),
        TableauStep(5, 3, "beta", Not(conj), (Not(Atom("Q", [c])),), branch_split=True),
    )
    closures = (TableauClosure(4, Not(P(c)), 4, P(c), 1),
                TableauClosure(5, Not(Atom("Q", [c])), 5, Atom("Q", [c]), 2))
    with pytest.raises(TableauCheckError, match="not fresh"):
        check_tableau_proof(TableauProof(roots, steps, closures), premises, conclusion)


def test_the_checker_compares_the_name_of_a_witness_with_every_kind_of_symbol():
    # a witness spelled like a function symbol of the root formulas is not fresh either: a
    # zero-argument function is the constant of its name in every writer of the kit
    f0 = Function("_t0", [])
    premises = [exists(x, P(x)), Z(f0)]
    conclusion = exists(y, P(y))
    c = Constant("_t0")
    roots = tuple(premises) + (Not(conclusion),)
    steps = (TableauStep(1, 0, "delta", premises[0], (P(c),), fresh_constant=c),
             TableauStep(2, 1, "gamma", roots[2], (Not(P(c)),), terms=(c,)))
    closures = (TableauClosure(2, Not(P(c)), 2, P(c), 1),)
    with pytest.raises(TableauCheckError, match="not fresh"):
        check_tableau_proof(TableauProof(roots, steps, closures), premises, conclusion)


def test_the_searched_proof_of_a_problem_with_clashing_constants_is_certified():
    premises = [exists(x, P(x)), Implies(P(Constant("_t0")), Z(Constant("zz")))]
    conclusion = Implies(Not(Z(Constant("zz"))), exists(y, P(y)))
    result = check_entailment_tableau_detailed(premises, conclusion)
    assert result["proved"] and result["check_passed"] is True, result["check_error"]
