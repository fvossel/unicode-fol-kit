"""Tests for unicode_fol_kit.eval.exercise_gen (roadmap C61) and the
unicode_fol_kit.semantics.modelfinder.is_size_exhaustive helper it needs.

Per this batch's test oracle, every generated exercise is re-checked by a
route INDEPENDENT of the generator's own internal call -- never "trust the
same search twice":

- valid/invalid pairs: a from-scratch propositional evaluator and a full
  ``2**n`` valuation enumeration, both written directly in this file (never
  calling ``semantics.truthtable``), plus a fresh
  ``semantics.tarski.Structure``/``models`` check for the invalid formula's
  countermodel.
- Fitch proofs: ``atp.fitch.check_proof`` (an independent, non-search
  verifier) and a nested-Subproof depth counter re-implemented from scratch
  in this file, calibrated against hand-built LEM / De Morgan derivations
  with hand-counted expected depths.
- Model-size theories: a dumb brute-force enumeration of every structure at
  each domain size below the target, written directly in this file (never
  touching ``semantics.modelfinder``'s own search code), plus a Z3
  "satisfiable with EXACTLY k elements" check at the target size and one
  below.
"""

import itertools

import pytest
import z3

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Quantifier, Variable, Z3Env, SortedQuantifier,
)
from unicode_fol_kit.fol.signature import Signature
from unicode_fol_kit.semantics.tarski import Structure, models
from unicode_fol_kit.semantics import modelfinder
from unicode_fol_kit.atp.fitch import (
    Proof, Subproof, assume, line, check_proof, FALSUM,
)
from unicode_fol_kit.eval.exercise_gen import (
    ValidInvalidPair, generate_valid_invalid_pair,
    EntailmentExercise, generate_entailment_with_proof,
    ModelSizeExercise, generate_theory_with_model_size,
)

# 5 nullary predicates (enough for target_depth up to 5) and 2 binary ones,
# shared by most tests below.
SIG = Signature.from_dict({
    "predicates": {"A": 0, "B": 0, "C": 0, "D": 0, "E": 0, "Rel": 2, "Ord": 2},
})
SIG_NO_NULLARY = Signature.from_dict({"predicates": {"Rel": 2}})
SIG_NO_BINARY = Signature.from_dict({"predicates": {"A": 0}})


# ===========================================================================
# 1. generate_valid_invalid_pair -- independent route: a from-scratch
#    propositional evaluator + full 2**n enumeration (not truthtable.py).
# ===========================================================================

def _atoms_of(node) -> set:
    if isinstance(node, Atom):
        return {node.to_unicode_str()}
    out: set = set()
    for child in node._child_nodes():
        out |= _atoms_of(child)
    return out


def _eval_prop(node, valuation: dict) -> bool:
    """A from-scratch classical-propositional evaluator over And/Or/Not/Implies/Atom."""
    if isinstance(node, Atom):
        return bool(valuation[node.to_unicode_str()])
    if isinstance(node, Not):
        return not _eval_prop(node.formula, valuation)
    if isinstance(node, And):
        return _eval_prop(node.left, valuation) and _eval_prop(node.right, valuation)
    if isinstance(node, Or):
        return _eval_prop(node.left, valuation) or _eval_prop(node.right, valuation)
    if isinstance(node, Implies):
        return (not _eval_prop(node.left, valuation)) or _eval_prop(node.right, valuation)
    raise TypeError(f"independent evaluator: unsupported node {type(node).__name__}")


def _is_tautology_independent(node) -> bool:
    atoms = sorted(_atoms_of(node))
    for bits in itertools.product((False, True), repeat=len(atoms)):
        if not _eval_prop(node, dict(zip(atoms, bits))):
            return False
    return True


def test_independent_evaluator_hand_checked():
    """Calibration for the independent evaluator itself, on two textbook
    one-atom cases worked out by hand: P -> P is true under both rows of its
    truth table (P=F: F->F=T; P=T: T->T=T), so it is a tautology. P & !P is
    false under both rows (P=F: F&T=F; P=T: T&F=F), so it never is."""
    P = Atom("P", ())
    assert _is_tautology_independent(Implies(P, P)) is True
    assert _is_tautology_independent(And(P, Not(P))) is False


def test_valid_invalid_pair_independently_checked_across_seeds():
    for seed in range(30):
        pair = generate_valid_invalid_pair(SIG, max_atoms=3, seed=seed)
        assert isinstance(pair, ValidInvalidPair)

        assert _is_tautology_independent(pair.valid_formula), (
            f"seed={seed}: 'valid' formula "
            f"{pair.valid_formula.to_unicode_str()!r} is not a tautology "
            "under independent 2**n enumeration"
        )
        assert not _is_tautology_independent(pair.invalid_formula), (
            f"seed={seed}: 'invalid' formula "
            f"{pair.invalid_formula.to_unicode_str()!r} IS a tautology "
            "under independent 2**n enumeration"
        )

        # The supplied countermodel genuinely falsifies invalid_formula,
        # under the from-scratch evaluator...
        assert _eval_prop(pair.invalid_formula, dict(pair.invalid_valuation)) is False
        # ...and under a SEPARATE evaluator this file did not write itself
        # (semantics.tarski.models), on a freshly built Structure.
        structure = Structure(
            domain=("*",),
            predicates={(name, 0): bool(v) for name, v in pair.invalid_valuation.items()},
        )
        assert models(pair.invalid_formula, structure) is False


def test_valid_invalid_pair_reproducible():
    a = generate_valid_invalid_pair(SIG, max_atoms=3, seed=777)
    b = generate_valid_invalid_pair(SIG, max_atoms=3, seed=777)
    assert a.valid_formula == b.valid_formula
    assert a.invalid_formula == b.invalid_formula
    assert a.invalid_valuation == b.invalid_valuation
    assert a.atoms == b.atoms
    assert a.valid_formula.to_unicode_str() == b.valid_formula.to_unicode_str()
    assert a.invalid_formula.to_unicode_str() == b.invalid_formula.to_unicode_str()


def test_valid_invalid_pair_different_seeds_can_differ():
    formulas = {
        generate_valid_invalid_pair(SIG, max_atoms=3, seed=s).valid_formula.to_unicode_str()
        for s in range(10)
    }
    assert len(formulas) > 1  # sampling is non-vacuous, not one fixed constant


def test_valid_invalid_pair_respects_max_atoms():
    pair = generate_valid_invalid_pair(SIG, max_atoms=2, seed=3)
    assert len(pair.atoms) == 2


def test_valid_invalid_pair_refuses_without_nullary_predicates():
    with pytest.raises(ValueError, match="nullary"):
        generate_valid_invalid_pair(SIG_NO_NULLARY)


def test_valid_invalid_pair_refuses_bad_max_atoms():
    with pytest.raises(ValueError):
        generate_valid_invalid_pair(SIG, max_atoms=0)


# ===========================================================================
# 2. generate_entailment_with_proof -- independent route: atp.fitch.check_proof
#    (a non-search verifier) + a from-scratch nested-Subproof depth counter.
# ===========================================================================

def _nesting_depth_independent(steps) -> int:
    """A from-scratch nested-Subproof counter (independent of
    exercise_gen._nesting_depth): two SIBLING subproofs at the same level
    both count once, not twice -- see the De Morgan case below."""
    depth = 0
    for step in steps:
        if isinstance(step, Subproof):
            depth = max(depth, 1 + _nesting_depth_independent(step.body))
    return depth


def _lem_proof() -> Proof:
    """⊢ P ∨ ¬P via RAA (excluded middle). Hand-counted nesting depth: the
    outer Subproof (assuming ¬(P∨¬P)) itself CONTAINS an inner Subproof
    (assuming P) in its body -> nesting depth 2."""
    P = Atom("P", ())
    return Proof(steps=[
        Subproof(
            assumption=assume(1, Not(Or(P, Not(P)))),
            body=[
                Subproof(assumption=assume(2, P),
                        body=[line(3, Or(P, Not(P)), "∨I", 2),
                              line(4, FALSUM, "⊥I", 3, 1)]),
                line(5, Not(P), "¬I", (2, 4)),
                line(6, Or(P, Not(P)), "∨I", 5),
                line(7, FALSUM, "⊥I", 6, 1),
            ],
        ),
        line(8, Or(P, Not(P)), "RAA", (1, 7)),
    ])


def _demorgan_proof() -> Proof:
    """¬(P∨Q) ⊢ ¬P∧¬Q (one De Morgan direction). Hand-counted nesting depth:
    two SIBLING Subproofs (assuming P, assuming Q respectively), neither
    contained in the other -> nesting depth 1, not 2."""
    P, Q = Atom("P", ()), Atom("Q", ())
    return Proof(
        premises=[line(1, Not(Or(P, Q)), "Premise")],
        steps=[
            Subproof(assumption=assume(2, P),
                    body=[line(3, Or(P, Q), "∨I", 2), line(4, FALSUM, "⊥I", 3, 1)]),
            line(5, Not(P), "¬I", (2, 4)),
            Subproof(assumption=assume(6, Q),
                    body=[line(7, Or(P, Q), "∨I", 6), line(8, FALSUM, "⊥I", 7, 1)]),
            line(9, Not(Q), "¬I", (6, 8)),
            line(10, And(Not(P), Not(Q)), "∧I", 5, 9),
        ],
    )


def test_depth_counter_calibrated_against_textbook_proofs():
    lem = _lem_proof()
    assert check_proof(lem)
    assert _nesting_depth_independent(lem.steps) == 2

    dm = _demorgan_proof()
    assert check_proof(dm)
    assert _nesting_depth_independent(dm.steps) == 1


@pytest.mark.parametrize("depth", [1, 2, 3, 4, 5])
def test_generate_entailment_with_proof_depth_and_soundness(depth):
    ex = generate_entailment_with_proof(SIG, target_depth=depth, seed=depth * 97 + 3)
    assert isinstance(ex, EntailmentExercise)
    assert ex.depth == depth

    # Independent check #1: a from-scratch nesting-depth count on the raw
    # Proof.steps, never calling exercise_gen's own counter.
    assert _nesting_depth_independent(ex.proof.steps) == depth

    # Independent check #2: atp.fitch.check_proof, a fresh, non-search
    # verification pass on the returned Proof object.
    assert check_proof(ex.proof)

    assert ex.proof.premises == ()
    assert ex.conclusion is not None
    assert ex.premises == ()


def test_generate_entailment_with_proof_reproducible():
    a = generate_entailment_with_proof(SIG, target_depth=3, seed=555)
    b = generate_entailment_with_proof(SIG, target_depth=3, seed=555)
    assert a.proof == b.proof
    assert a.conclusion == b.conclusion
    assert a.proof.to_fitch() == b.proof.to_fitch()


def test_generate_entailment_with_proof_refuses_bad_depth():
    with pytest.raises(ValueError):
        generate_entailment_with_proof(SIG, target_depth=0)


def test_generate_entailment_with_proof_refuses_insufficient_predicates():
    with pytest.raises(ValueError, match="nullary"):
        generate_entailment_with_proof(SIG, target_depth=6)  # SIG has only 5


# ===========================================================================
# 3. generate_theory_with_model_size -- independent route: a dumb brute-force
#    enumeration of every structure below the target size, plus a Z3
#    "exactly k elements" satisfiability check.
# ===========================================================================

def _brute_force_has_model(theory, relation: str, k: int) -> bool:
    """Try EVERY possible extension of the binary ``relation`` over domain
    ``range(k)`` and return True iff some extension satisfies every formula
    in ``theory``. A dumb, from-scratch enumeration -- never imports or calls
    semantics.modelfinder, only Structure/models."""
    domain = tuple(range(k))
    pairs = [(a, b) for a in domain for b in domain]
    for mask in range(1 << len(pairs)):
        ext = {pairs[i] for i in range(len(pairs)) if (mask >> i) & 1}
        structure = Structure(domain=domain, predicates={(relation, 2): ext})
        if all(models(f, structure) for f in theory):
            return True
    return False


def _z3_exact_size_sat(formulas, k: int) -> bool:
    """True iff ``formulas`` are jointly satisfiable in a structure with
    EXACTLY ``k`` elements, decided directly by Z3 (independent of
    semantics.modelfinder's brute-force search): ``k`` pairwise-distinct
    fresh constants, plus a totality axiom saying every element of the sort
    equals one of them."""
    env = Z3Env()
    solver = z3.Solver()
    solver.set("timeout", 10000)
    for f in formulas:
        solver.add(f.to_z3(env))
    sort = env.get_symbol("_sort_probe").sort()
    us = [z3.Const(f"_u{i}", sort) for i in range(k)]
    for i in range(k):
        for j in range(i + 1, k):
            solver.add(us[i] != us[j])
    xvar = z3.Const("_x", sort)
    solver.add(z3.ForAll([xvar], z3.Or(*[xvar == u for u in us])))
    return solver.check() == z3.sat


@pytest.mark.parametrize("target_size", [1, 2, 3, 4])
def test_generate_theory_with_model_size(target_size):
    ex = generate_theory_with_model_size(SIG, target_size=target_size, seed=target_size + 9)
    assert isinstance(ex, ModelSizeExercise)
    assert ex.target_size == target_size
    assert len(ex.witness.domain) == target_size

    # Independent check #1: the witness genuinely satisfies the theory under
    # a fresh models() call (the generator's own internal check is not reused).
    for f in ex.theory:
        assert models(f, ex.witness)

    # Independent check #2: dumb brute-force enumeration (this file's own
    # code, not modelfinder's) finds no model at any size below the target.
    for k in range(1, target_size):
        assert not _brute_force_has_model(ex.theory, ex.relation, k), (
            f"target_size={target_size}: brute force found a model at size {k}"
        )

    # Independent check #3: Z3, asked directly whether the theory is
    # satisfiable with EXACTLY k elements -- sat at the target, unsat one below.
    assert _z3_exact_size_sat(ex.theory, target_size)
    if target_size > 1:
        assert not _z3_exact_size_sat(ex.theory, target_size - 1)


def test_generate_theory_with_model_size_hand_checked_order_needs_two():
    """Hand-checked textbook fact, the one the roadmap's own test oracle
    names: an irreflexive total order needs domain size >= 2. At size 1 the
    only candidate relation extensions are R={} and R={(0,0)}; irreflexivity
    rules out the second, and with R={} the target_size=2 chain constraint
    (which needs two DISTINCT elements x1 R x2) cannot be satisfied by a
    single element either way -- brute-forced over both extensions below."""
    ex = generate_theory_with_model_size(SIG, target_size=2, seed=5)
    assert len(ex.witness.domain) == 2
    assert not _brute_force_has_model(ex.theory, ex.relation, 1)
    assert _z3_exact_size_sat(ex.theory, 2)
    assert not _z3_exact_size_sat(ex.theory, 1)


def test_generate_theory_with_model_size_refuses_without_binary_predicate():
    with pytest.raises(ValueError, match="binary"):
        generate_theory_with_model_size(SIG_NO_BINARY, target_size=2)


def test_generate_theory_with_model_size_refuses_bad_target_size():
    with pytest.raises(ValueError):
        generate_theory_with_model_size(SIG, target_size=0)


def test_generate_theory_with_model_size_refuses_when_budget_exceeded():
    """A binary relation's candidate count grows as 2**(k*k); at the default
    budget (2**20) this loudly refuses well before target_size gets large
    (see is_size_exhaustive's own hand-counted test below: size 5 alone
    already needs 2**25 candidates) rather than silently mis-claim a smaller
    'minimal' size than it actually certified."""
    with pytest.raises(ValueError, match="max_candidates"):
        generate_theory_with_model_size(SIG, target_size=5, seed=1)


def test_generate_theory_with_model_size_reproducible():
    a = generate_theory_with_model_size(SIG, target_size=3, seed=123)
    b = generate_theory_with_model_size(SIG, target_size=3, seed=123)
    assert a.theory == b.theory
    assert a.relation == b.relation
    assert a.witness.domain == b.witness.domain
    assert a.witness.predicates == b.witness.predicates


# ===========================================================================
# 4. modelfinder.is_size_exhaustive -- the skipped-vs-refuted honesty helper.
# ===========================================================================

def test_is_size_exhaustive_hand_counted_nullary():
    """One 0-ary predicate: its raw interpretation count is 2**1 = 2 at
    EVERY domain size k (arity 0 never scales with k)."""
    theory = [Atom("A", ())]
    assert modelfinder.is_size_exhaustive(theory, 1, max_candidates=2)
    assert not modelfinder.is_size_exhaustive(theory, 1, max_candidates=1)
    assert modelfinder.is_size_exhaustive(theory, 5, max_candidates=2)
    assert not modelfinder.is_size_exhaustive(theory, 5, max_candidates=1)


def test_is_size_exhaustive_hand_counted_binary_relation():
    """One binary predicate, no constants: symmetry breaking cannot reduce a
    predicate table at all (only CONSTANTS are LNH-reduced -- see
    modelfinder's own module docstring), so the count at domain size k is
    exactly 2**(k*k), hand-computed: k=1 -> 2, k=2 -> 16, k=3 -> 512."""
    x, y = Variable("x"), Variable("y")
    theory = [Quantifier("∀", x, Quantifier("∀", y, Atom("R", (x, y))))]
    assert modelfinder.is_size_exhaustive(theory, 1, max_candidates=2)
    assert not modelfinder.is_size_exhaustive(theory, 1, max_candidates=1)
    assert modelfinder.is_size_exhaustive(theory, 2, max_candidates=16)
    assert not modelfinder.is_size_exhaustive(theory, 2, max_candidates=15)
    assert modelfinder.is_size_exhaustive(theory, 3, max_candidates=512)
    assert not modelfinder.is_size_exhaustive(theory, 3, max_candidates=511)


def test_is_size_exhaustive_catches_the_skip_vs_refuted_conflation():
    """The scenario is_size_exhaustive exists to expose: a theory genuinely
    SATISFIABLE at size 3, but with a budget too small to search size 3, so
    find_model(max_size=3, max_candidates=100) returns None -- indistinguishable,
    from the outside, from a genuine 'unsatisfiable up to size 3'. A caller
    who additionally checks is_size_exhaustive at size 3 sees False and knows
    NOT to trust that None; raising the budget confirms a model really does
    exist at size 3 (so the None truly was a skip, not a refutation)."""
    x = Variable("x")
    v = [Variable(f"v{i}") for i in range(3)]
    # A benign, always-true mention of R so it enters the theory's signature
    # (and hence its candidate count) without constraining satisfiability.
    tauto_r = Quantifier("∀", x, Or(Atom("R", (x, x)), Not(Atom("R", (x, x)))))
    pairwise_distinct = And(Atom("≠", (v[0], v[1])),
                            And(Atom("≠", (v[0], v[2])), Atom("≠", (v[1], v[2]))))
    forces_three = pairwise_distinct
    for var in reversed(v):
        forces_three = Quantifier("∃", var, forces_three)
    theory = [tauto_r, forces_three]

    assert modelfinder.is_size_exhaustive(theory, 1, max_candidates=100)
    assert modelfinder.is_size_exhaustive(theory, 2, max_candidates=100)
    assert not modelfinder.is_size_exhaustive(theory, 3, max_candidates=100)  # 2**9=512 > 100

    assert modelfinder.find_model(theory, max_size=3, max_candidates=100) is None
    witness = modelfinder.find_model(theory, max_size=3, max_candidates=1000)
    assert witness is not None and len(witness.domain) == 3


def test_is_size_exhaustive_hand_counted_sorted():
    """A many-sorted (MSFOL) theory exercises is_size_exhaustive's OTHER
    branch (``sig.sorts`` truthy), which generate_theory_with_model_size
    itself never reaches (it only ever builds an unsorted theory) and so has
    no coverage from the generator's own tests above.

    Theory: ``forall x:Human Mortal(x)`` -- one sort ("Human"), one unary
    predicate ("Mortal", arity 1), zero constants. Per _candidate_count's own
    formula (module docstring's "Subsorting" section: a sort contributes
    ``(2**k - 1)`` non-empty-subset universe choices, a predicate of arity a
    contributes ``2**(k**a)`` interpretations, both UNREDUCED here because the
    sorted branch ignores symmetry_breaking entirely -- see is_size_exhaustive's
    own docstring), the count at domain size k is
    ``2**k * (2**k - 1)``, hand-computed:
      k=1: 2**1 * (2**1 - 1) =  2 *  1 =  2
      k=2: 2**2 * (2**2 - 1) =  4 *  3 = 12
      k=3: 2**3 * (2**3 - 1) =  8 *  7 = 56
    """
    x = Variable("x")
    theory = [SortedQuantifier("∀", x, "Human", Atom("Mortal", (x,)))]

    assert modelfinder.is_size_exhaustive(theory, 1, max_candidates=2)
    assert not modelfinder.is_size_exhaustive(theory, 1, max_candidates=1)
    assert modelfinder.is_size_exhaustive(theory, 2, max_candidates=12)
    assert not modelfinder.is_size_exhaustive(theory, 2, max_candidates=11)
    assert modelfinder.is_size_exhaustive(theory, 3, max_candidates=56)
    assert not modelfinder.is_size_exhaustive(theory, 3, max_candidates=55)

    # The sorted branch documents that it ignores symmetry_breaking (find_model
    # itself never LNH-reduces sorted search) -- pin that the flag really makes
    # no difference here, unlike the unsorted hand-counted tests above.
    for k, exact in ((1, 2), (2, 12), (3, 56)):
        assert (modelfinder.is_size_exhaustive(theory, k, max_candidates=exact,
                                               symmetry_breaking=True)
                == modelfinder.is_size_exhaustive(theory, k, max_candidates=exact,
                                                  symmetry_breaking=False)
                == True)

    # Cross-check against find_model's own pre-flight at the boundary: size 3
    # is exhaustive at max_candidates=56 (a model must be found, or the theory
    # is genuinely unsatisfiable there -- not merely skipped), and this theory
    # IS satisfiable (any non-empty Human universe with Mortal true everywhere
    # on it works), so find_model must actually return a witness.
    witness = modelfinder.find_model(theory, max_size=3, max_candidates=56)
    assert witness is not None
    assert "Human" in witness.sorts and 1 <= len(witness.sorts["Human"]) <= 3
