"""Tests for the independent tableau-proof checker (unicode_fol_kit.atp.tableau_check)
and the proof object it checks (unicode_fol_kit.atp.tableau.TableauProof /
prove_tableau_detailed).

Every hand-checked case below traces :func:`prove_tableau_detailed`'s recorded
tree by hand against ``_close``'s own documented rule semantics (see
``atp/tableau.py``'s module docstring) BEFORE asserting on step counts/shapes —
the derivation is written out in each test's docstring/comments, not lifted
from running the code first. Four families of tests:

- Positive cases: modus ponens, ∀-instantiation, an ∃/δ-witness case, a
  branching (β) case with two independently-derived closures, and an
  empty-premises (pure tautology) case — each with its full hand-derived tree.
- A prove -> check round trip over ~10 mixed valid sequences (propositional,
  ∀/∃, β-connectives Or/Iff/Xor, nested quantifiers).
- A regression check that :func:`prove_tableau`'s own verdicts (the function
  this task must leave byte-for-byte untouched) are unchanged, and that its
  verdict always agrees with ``prove_tableau_detailed(...) is not None``.
- A tamper suite (>= 8 variants): each mutates one field of an otherwise-valid
  recorded proof and asserts the checker rejects it, with an assertion on the
  particular failure reason.
"""

import pytest
from dataclasses import replace

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import substitute
from unicode_fol_kit.atp.tableau import (
    prove_tableau, prove_tableau_detailed, TableauStep, TableauClosure, TableauProof,
)
from unicode_fol_kit.atp.tableau_check import (
    check_tableau_proof, check_entailment_tableau_detailed, TableauCheckError,
)

_P = MSFLParser()


def parse_all(strings):
    return [_P.parse(s) for s in strings]


# ---------------------------------------------------------------------------
# Positive cases, hand-derived
# ---------------------------------------------------------------------------

def test_modus_ponens_proof():
    """{P(a) → Q(a), P(a)} ⊨ Q(a). root = [P(a)→Q(a), P(a), ¬Q(a)].

    P(a)→Q(a) is a β-formula: alternatives [¬P(a)] / [Q(a)].
      left  (step 1, parent 0): adds ¬P(a); ¬P(a)'s complement P(a) is root
            formula #1 (id 0) -> closes at node 1.
      right (step 2, parent 0): adds Q(a); Q(a)'s complement ¬Q(a) is root
            formula #2 (id 0) -> closes at node 2.
    2 steps, 2 closures, both leaves closed.
    """
    prems = parse_all(["P(a) → Q(a)"]) + parse_all(["P(a)"])
    concl = _P.parse("Q(a)")
    proof = prove_tableau_detailed(prems, concl)
    assert proof is not None
    assert len(proof.steps) == 2
    assert len(proof.closures) == 2
    assert all(s.rule == "beta" and s.branch_split for s in proof.steps)
    assert {s.parent_id for s in proof.steps} == {0}
    check_tableau_proof(proof, prems, concl)  # must not raise


def test_forall_instantiation_proof():
    """{∀x(P(x)→Q(x)), P(a)} ⊨ Q(a). root = [∀x(P(x)→Q(x)), P(a), ¬Q(a)].

    Step 1 (γ, parent 0): the universal instantiated at the only ground term
      in scope (a) -> P(a)→Q(a).
    That is a β-formula: step 2 (parent 1) adds ¬P(a), closing against root
      formula P(a); step 3 (parent 1) adds Q(a), closing against root formula
      ¬Q(a). 3 steps, 2 closures.
    """
    prems = parse_all(["∀x (P(x) → Q(x))", "P(a)"])
    concl = _P.parse("Q(a)")
    proof = prove_tableau_detailed(prems, concl)
    assert proof is not None
    assert len(proof.steps) == 3
    assert len(proof.closures) == 2
    assert proof.steps[0].rule == "gamma" and len(proof.steps[0].terms) == 1
    assert proof.steps[0].terms[0].to_unicode_str() == "a"
    check_tableau_proof(proof, prems, concl)


def test_exists_delta_proof():
    """{∃x P(x)} ⊨ ¬∀x ¬P(x). root = [∃x P(x), ¬¬∀x ¬P(x)].

    Step 1 (δ, parent 0): ∃x P(x) witnessed by a fresh constant t0 -> P(t0).
    Step 2 (α, parent 1): the double negation ¬¬∀x ¬P(x) -> ∀x ¬P(x).
    Step 3 (γ, parent 2): ∀x ¬P(x) instantiated at the only ground term now on
      the branch (t0, introduced by step 1) -> ¬P(t0), which is P(t0)'s
      complement (produced by step 1) -> closes at node 3.
    3 steps, 1 closure; this is the rule surface's classical soundness trap
    (a δ-witness must be genuinely fresh) exercised in the SIMPLEST shape.
    """
    prems = parse_all(["∃x P(x)"])
    concl = _P.parse("¬∀x ¬P(x)")
    proof = prove_tableau_detailed(prems, concl)
    assert proof is not None
    assert len(proof.steps) == 3
    assert len(proof.closures) == 1
    assert proof.steps[0].rule == "delta"
    fresh = proof.steps[0].fresh_constant
    assert proof.steps[2].rule == "gamma" and proof.steps[2].terms == (fresh,)
    check_tableau_proof(proof, prems, concl)


def test_branching_two_independent_closures():
    """{P ↔ Q, P} ⊨ Q. root = [P↔Q, P, ¬Q].

    P↔Q is a β-formula: alternatives [P, Q] / [¬P, ¬Q].
      left  (step 1, parent 0): adds P, Q; Q's complement ¬Q is root formula
            #2 -> closes at node 1 via (¬Q, Q).
      right (step 2, parent 0): adds ¬P, ¬Q; ¬P's complement P is root
            formula #1 -> closes at node 2 via (P, ¬P).
    Two branches, two INDEPENDENT closure pairs (different literal/complement
    formulas each), both under the very first β split.
    """
    prems = parse_all(["P ↔ Q", "P"])
    concl = _P.parse("Q")
    proof = prove_tableau_detailed(prems, concl)
    assert proof is not None
    assert len(proof.steps) == 2
    assert len(proof.closures) == 2
    lits = {c.literal for c in proof.closures}
    assert lits == {_P.parse("¬Q"), _P.parse("P")}
    check_tableau_proof(proof, prems, concl)


def test_empty_premises_tautology():
    """{} ⊨ P(a) ∨ ¬P(a). root = [¬(P(a) ∨ ¬P(a))] (premises contribute nothing).

    Step 1 (α, parent 0): ¬(A ∨ B) -> ¬A, ¬¬A (A = P(a)) -> produces ¬P(a), ¬¬P(a).
    Step 2 (α, parent 1): the double negation ¬¬P(a) -> P(a), which is ¬P(a)'s
      (step 1's own) complement -> closes at node 2.
    2 steps, 1 closure — the smallest genuine test of an empty premise list.
    """
    proof = prove_tableau_detailed([], _P.parse("P(a) ∨ ¬P(a)"))
    assert proof is not None
    assert proof.root_formulas == (_P.parse("¬(P(a) ∨ ¬P(a))"),)
    assert len(proof.steps) == 2
    assert len(proof.closures) == 1
    check_tableau_proof(proof, [], _P.parse("P(a) ∨ ¬P(a)"))


# ---------------------------------------------------------------------------
# Round trip: prove_tableau_detailed -> check_tableau_proof, over ~10 mixed
# valid sequences (propositional, ∀/∃, every β-connective, nested quantifiers).
# ---------------------------------------------------------------------------

_ROUND_TRIP_CASES = [
    (["P(a) → Q(a)", "P(a)"], "Q(a)"),
    (["∀x (P(x) → Q(x))", "P(tom)"], "Q(tom)"),
    ([], "∀x P(x) → P(tom)"),
    ([], "∃x ∀y R(x, y) → ∀y ∃x R(x, y)"),
    (["∃x P(x)"], "¬∀x ¬P(x)"),
    (["P ↔ Q", "P"], "Q"),
    (["P ∨ Q", "¬P"], "Q"),
    (["∀x (P(x) ↔ Q(x))", "P(a)"], "Q(a)"),
    (["P → Q", "Q → R", "P"], "R"),
    (["∀x ∃y R(x, y)"], "∃y R(a, y)"),
    (["P ⊕ Q", "P"], "¬Q"),
]


@pytest.mark.parametrize("premises,goal", _ROUND_TRIP_CASES)
def test_round_trip_prove_then_check(premises, goal):
    prems = parse_all(premises)
    concl = _P.parse(goal)
    assert prove_tableau(prems, concl), "fixture is meant to be tableau-provable"
    proof = prove_tableau_detailed(prems, concl)
    assert proof is not None
    check_tableau_proof(proof, prems, concl)  # must not raise
    result = check_entailment_tableau_detailed(prems, concl)
    assert result == {"proved": True, "proof": proof, "check_passed": True, "check_error": None}


# ---------------------------------------------------------------------------
# Regression: prove_tableau's own verdicts must be exactly as before, and
# always agree with prove_tableau_detailed(...) is not None.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("premises,goal,entailed", [
    (["∀x (P(x) → Q(x))", "P(tom)"], "Q(tom)", True),
    ([], "∀x P(x) → P(tom)", True),
    ([], "∃x ∀y R(x, y) → ∀y ∃x R(x, y)", True),
    ([], "∀y ∃x R(x, y) → ∃x ∀y R(x, y)", False),
    ([], "∃x P(x) → ∀x P(x)", False),
])
def test_prove_tableau_unchanged(premises, goal, entailed):
    """Pinned from tests/test_new_subsystems.py::test_tableau_fol — prove_tableau
    must return the exact same verdicts after this task's additions."""
    prems = parse_all(premises)
    concl = _P.parse(goal)
    assert prove_tableau(prems, concl) is entailed


@pytest.mark.parametrize("premises,goal", [c for c in _ROUND_TRIP_CASES] + [
    ([], "∀y ∃x R(x, y) → ∃x ∀y R(x, y)"),
    ([], "∃x P(x) → ∀x P(x)"),
    (["P(a)"], "Q(a)"),
])
def test_prove_tableau_agrees_with_detailed(premises, goal):
    prems = parse_all(premises)
    concl = _P.parse(goal)
    assert prove_tableau(prems, concl) == (prove_tableau_detailed(prems, concl) is not None)


def test_check_entailment_tableau_detailed_unprovable():
    prems = parse_all(["∃x P(x)"])
    concl = _P.parse("∀x P(x)")
    result = check_entailment_tableau_detailed(prems, concl)
    assert result == {"proved": False, "proof": None, "check_passed": None, "check_error": None}


# ---------------------------------------------------------------------------
# Tamper suite (>= 8 variants). Each starts from a genuine proof and mutates
# exactly one thing, asserting the checker rejects it with the matching
# reason.
# ---------------------------------------------------------------------------

def _mp_proof():
    prems = parse_all(["P(a) → Q(a)", "P(a)"])
    concl = _P.parse("Q(a)")
    proof = prove_tableau_detailed(prems, concl)
    assert proof is not None
    return prems, concl, proof


def _exists_delta_reinstantiation_proof():
    """{∀x(P(x)→Q(x)), ∃x P(x)} ⊨ ∃x Q(x)} — has both a delta AND a
    later-reinstantiated gamma step, needed by the freshness/substitution
    tamper tests below."""
    prems = parse_all(["∀x (P(x) → Q(x))", "∃x P(x)"])
    concl = _P.parse("∃x Q(x)")
    proof = prove_tableau_detailed(prems, concl)
    assert proof is not None
    return prems, concl, proof


def test_tamper_wrong_complement():
    """Closure's complement replaced by an unrelated (non-complementary) formula."""
    prems, concl, proof = _mp_proof()
    c0 = proof.closures[0]
    bad = replace(proof, closures=(replace(c0, complement=_P.parse("Q(a)")),) + proof.closures[1:])
    with pytest.raises(TableauCheckError, match="does not actually occur|not complementary"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_closure_pair_not_on_branch():
    """Closure cites a node that is not an ancestor of its own leaf."""
    prems, concl, proof = _mp_proof()
    c0 = proof.closures[0]
    other_step_id = proof.closures[1].leaf_id  # a real step id, but off THIS branch
    bad = replace(proof, closures=(replace(c0, literal_step_id=other_step_id),) + proof.closures[1:])
    with pytest.raises(TableauCheckError, match="not on the branch"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_missing_closure_of_a_branch():
    """One leaf's closure is simply dropped -> an open branch slips through."""
    prems, concl, proof = _mp_proof()
    bad = replace(proof, closures=proof.closures[1:])
    with pytest.raises(TableauCheckError, match="no recorded closure \\(open branch\\)"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_delta_constant_not_fresh():
    """A delta step's witnessing constant is set to one already on ITS OWN branch."""
    prems, concl, proof = _exists_delta_reinstantiation_proof()
    delta_steps = [s for s in proof.steps if s.rule == "delta"]
    target = delta_steps[1]
    # A gamma term genuinely on target's own ancestor chain (its sibling gamma
    # step's instantiation), so reusing it is a REAL same-branch collision.
    ancestor_ids = []
    cur = target.parent_id
    steps_by_id = {s.step_id: s for s in proof.steps}
    while cur != 0:
        ancestor_ids.append(cur)
        cur = steps_by_id[cur].parent_id
    reused = next(t for sid in ancestor_ids for t in steps_by_id[sid].terms)
    var, body = target.principal_formula.variable, target.principal_formula.formula
    bad_step = replace(target, fresh_constant=reused, produced=(substitute(body, var, reused),))
    bad_steps = tuple(bad_step if s.step_id == target.step_id else s for s in proof.steps)
    bad = replace(proof, steps=bad_steps)
    with pytest.raises(TableauCheckError, match="not fresh"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_gamma_substitution_wrong():
    """A gamma step's produced formula does not match substituting its own term."""
    prems, concl, proof = _exists_delta_reinstantiation_proof()
    g = next(s for s in proof.steps if s.rule == "gamma" and s.terms)
    bogus = (_P.parse("Z(nonsense)"),) + g.produced[1:]
    bad_step = replace(g, produced=bogus)
    bad_steps = tuple(bad_step if s.step_id == g.step_id else s for s in proof.steps)
    bad = replace(proof, steps=bad_steps)
    with pytest.raises(TableauCheckError, match="substitution does not check out"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_root_conclusion_not_negated():
    """Root's last formula is the bare conclusion instead of its negation."""
    prems, concl, proof = _mp_proof()
    bad = replace(proof, root_formulas=tuple(prems) + (concl,))
    with pytest.raises(TableauCheckError, match="negated conclusion"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_wrong_rule_assignment():
    """A beta step's rule field is overwritten to 'alpha'."""
    prems, concl, proof = _mp_proof()
    s0 = proof.steps[0]
    bad_step = replace(s0, rule="alpha")
    bad = replace(proof, steps=(bad_step,) + proof.steps[1:])
    with pytest.raises(TableauCheckError, match="branch_split"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_alpha_produced_formula_falsified():
    """An alpha step's produced conjunct is swapped for an unrelated formula."""
    prems = parse_all(["P(a) ∧ Q(a)"])
    concl = _P.parse("P(a)")
    proof = prove_tableau_detailed(prems, concl)
    assert proof is not None
    s_alpha = next(s for s in proof.steps if s.rule == "alpha")
    bad_step = replace(s_alpha, produced=(_P.parse("Z(a)"), s_alpha.produced[1]))
    bad_steps = tuple(bad_step if s.step_id == s_alpha.step_id else s for s in proof.steps)
    bad = replace(proof, steps=bad_steps)
    with pytest.raises(TableauCheckError, match="not the principal formula's own components"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_closure_references_non_leaf():
    """A closure is pointed at an internal node that still has further steps."""
    prems, concl, proof = _mp_proof()
    c0 = proof.closures[0]
    # Node 0 (the root) has children (steps 1 and 2) -- not a leaf.
    bad = replace(proof, closures=(replace(c0, leaf_id=0),) + proof.closures[1:])
    with pytest.raises(TableauCheckError, match="not a leaf"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_step_id_out_of_order():
    """Step IDs are not the 1-based sequence matching derivation position."""
    prems, concl, proof = _mp_proof()
    bad_step = replace(proof.steps[0], step_id=5)
    bad = replace(proof, steps=(bad_step,) + proof.steps[1:])
    with pytest.raises(TableauCheckError, match="1-based position"):
        check_tableau_proof(bad, prems, concl)


def test_tamper_fabricated_alpha_principal_not_on_branch():
    """THE adversarial-review checker hole (Tier-3 review, confirmed): a
    fabricated proof "decomposes" an INVENTED contradiction R(a) ∧ ¬R(a) —
    a formula that appears on no branch at all — and closes on its own two
    components. Every shape check passes (the produced formulas ARE the
    invented conjunction's conjuncts, the closure pair IS complementary and
    genuinely produced by step 1), so before the branch-membership check
    this certified the NON-entailment P(a) ⊨ Q(a). It must now be rejected
    because the principal formula is neither a root formula nor produced by
    any ancestor."""
    prems = parse_all(["P(a)"])
    concl = _P.parse("Q(a)")
    invented = _P.parse("R(a) ∧ ¬R(a)")
    fake = TableauProof(
        root_formulas=tuple(prems) + (_P.parse("¬Q(a)"),),
        steps=(TableauStep(step_id=1, parent_id=0, rule="alpha",
                           principal_formula=invented,
                           produced=(_P.parse("R(a)"), _P.parse("¬R(a)"))),),
        closures=(TableauClosure(leaf_id=1, literal=_P.parse("R(a)"),
                                 literal_step_id=1,
                                 complement=_P.parse("¬R(a)"),
                                 complement_step_id=1),))
    with pytest.raises(TableauCheckError, match="not on the branch"):
        check_tableau_proof(fake, prems, concl)


def test_tamper_fabricated_beta_principal_not_on_branch():
    """The same fabrication through the β route: an invented disjunction
    R(a) ∨ ¬R(a) splits the root into two branches that could never close
    honestly — the split's shared principal formula must itself be on the
    branch, and the checker rejects it before even looking at the (equally
    bogus) closures."""
    prems = parse_all(["P(a)"])
    concl = _P.parse("Q(a)")
    invented = _P.parse("R(a) ∨ ¬R(a)")
    fake = TableauProof(
        root_formulas=tuple(prems) + (_P.parse("¬Q(a)"),),
        steps=(TableauStep(step_id=1, parent_id=0, rule="beta",
                           principal_formula=invented,
                           produced=(_P.parse("R(a)"),), branch_split=True),
               TableauStep(step_id=2, parent_id=0, rule="beta",
                           principal_formula=invented,
                           produced=(_P.parse("¬R(a)"),), branch_split=True)),
        closures=(TableauClosure(leaf_id=1, literal=_P.parse("R(a)"),
                                 literal_step_id=1,
                                 complement=_P.parse("¬R(a)"),
                                 complement_step_id=2),
                  TableauClosure(leaf_id=2, literal=_P.parse("¬R(a)"),
                                 literal_step_id=2,
                                 complement=_P.parse("R(a)"),
                                 complement_step_id=1)))
    with pytest.raises(TableauCheckError, match="not on the branch it splits"):
        check_tableau_proof(fake, prems, concl)
