"""Tests for unicode_logic_kit.eval.explain.explain_proof.

Every expected string below is either hand-derived from the semantics of the
proof it describes (see each test's docstring for the derivation), or
cross-checked against an independent route already trusted elsewhere in the
kit (``check_tableau_proof``, ``check_twee_proof``, the TSTP/Twee text
parsers) — never a snapshot of whatever the function happened to produce.

Covers all five proof shapes confirmed (by grepping every ``proof=``
assignment in ``unicode_logic_kit/atp/``) to actually reach ``Verdict.proof``
today: ``TableauProof`` (TableauBackend), ``TstpDerivation``
(VampireBackend/EProverBackend), ``TweeProof`` (TweeBackend), the
``{"kind": "z3_unsat_core", ...}`` dict (Z3Backend), and the
``{"kind": "cvc5_alethe", ...}`` dict (CVC5Backend).
"""

import pytest

from unicode_logic_kit.eval.explain import explain_proof
from unicode_logic_kit.fol.nodes import Atom, Not

from unicode_logic_kit.atp.tableau import (
    TableauClosure, TableauProof, prove_tableau_detailed,
)
from unicode_logic_kit.atp.tableau_check import check_tableau_proof
from unicode_logic_kit.atp.tstp import TstpDerivation, TstpStep, parse_tstp_derivation
from unicode_logic_kit.atp.twee_check import check_twee_proof
from unicode_logic_kit.atp.twee_entailment import parse_twee_proof
from unicode_logic_kit import MSFLParser

_FOL = MSFLParser()

P = Atom("P", [])
Q = Atom("Q", [])


# ---------------------------------------------------------------------------
# TableauProof: {P → Q, P} ⊢ Q, built by the real search (prove_tableau_detailed)
# and independently re-verified by check_tableau_proof before being explained
# ---------------------------------------------------------------------------

def _mp_premises_and_conclusion():
    """{P → Q, P} ⊢ Q. Root = [P → Q, P, ¬Q] (premises then ¬conclusion).
    P → Q is neither a literal nor a conjunctive/quantified shape, so the
    search's only applicable rule is 'beta' on P → Q, splitting into two
    sibling steps — ¬P (branch A) and Q (branch B). Branch A closes on root
    formula P (id 0) vs step 1's ¬P; branch B closes on root formula ¬Q
    (id 0) vs step 2's Q. Hence exactly 2 steps (both 'beta') and 2
    closures — hand-derived here, confirmed unchanged by check_tableau_proof
    in every test that uses it below."""
    from unicode_logic_kit.fol.nodes import Implies
    return [Implies(P, Q), P], Q


def test_tableau_proof_reports_steps_rules_branches_and_closures():
    premises, conclusion = _mp_premises_and_conclusion()
    proof = prove_tableau_detailed(premises, conclusion)
    check_tableau_proof(proof, premises, conclusion)   # independent oracle; raises on failure

    text = explain_proof(proof)
    assert "The tableau proof has 2 steps." in text
    assert "Rule usage: beta (2)." in text
    assert "The proof has 2 closed branches." in text
    # Closures sorted by leaf_id: leaf 1 closes P against ¬P, leaf 2 closes ¬Q against Q.
    assert "Branch closing at node 1 closes P against ¬P." in text
    assert "Branch closing at node 2 closes ¬Q against Q." in text
    assert text.index("node 1") < text.index("node 2")   # sorted by leaf_id


def test_tableau_closure_sentences_match_checker_validated_closure_data():
    """Cross-check: every closure sentence must literally reproduce the
    Unicode rendering of the SAME literal/complement pair check_tableau_proof
    just certified as genuinely on that closed branch — sourced from
    proof.closures itself, not re-derived by hand a second time."""
    premises, conclusion = _mp_premises_and_conclusion()
    proof = prove_tableau_detailed(premises, conclusion)
    check_tableau_proof(proof, premises, conclusion)

    text = explain_proof(proof)
    for closure in proof.closures:
        literal_str = closure.literal.to_unicode_str()
        assert literal_str in text
        if closure.complement is not None:
            complement_str = closure.complement.to_unicode_str()
            assert f"closes {literal_str} against {complement_str}." in text


def test_tableau_proof_dict_matches_typed_object():
    """Verdict.proof carries proof.to_dict() once round-tripped through the
    process-pool boundary (see atp.portfolio._verdict_from_dict) — the dict
    form must explain identically to the typed object."""
    premises, conclusion = _mp_premises_and_conclusion()
    proof = prove_tableau_detailed(premises, conclusion)
    assert explain_proof(proof) == explain_proof(proof.to_dict())


def test_tableau_self_closing_branch_on_falsum_reported_directly():
    """A branch closing on a bare ⊥ (TableauClosure.complement is None per its
    own docstring) must not invent a complement — hand-built minimal proof,
    independently re-verified by check_tableau_proof."""
    falsum = Atom("⊥", ())
    root = (falsum, Not(Q))
    proof = TableauProof(root_formulas=root, steps=(), closures=(
        TableauClosure(leaf_id=0, literal=falsum, literal_step_id=0),
    ))
    check_tableau_proof(proof, [falsum], Q)

    text = explain_proof(proof)
    assert "The tableau proof has 0 steps." in text
    assert "Rule usage" not in text          # no steps means no histogram to report
    assert "The proof has 1 closed branch." in text
    assert "Branch closing at node 0 closes directly on ⊥." in text


def test_tableau_max_sentences_caps_output_to_the_priority_prefix():
    premises, conclusion = _mp_premises_and_conclusion()
    proof = prove_tableau_detailed(premises, conclusion)
    text = explain_proof(proof, max_sentences=1)
    assert text == "The tableau proof has 2 steps."


def test_tableau_explanation_is_deterministic():
    premises, conclusion = _mp_premises_and_conclusion()
    proof = prove_tableau_detailed(premises, conclusion)
    assert explain_proof(proof) == explain_proof(proof)


# ---------------------------------------------------------------------------
# TstpDerivation: hand-built TSTP text parsed through the real (independent)
# parser, exactly mirroring test_tstp.py's own captured-shape conventions
# ---------------------------------------------------------------------------

_TSTP_ONE_INFERENCE = """\
fof(f1,axiom,(p)).
fof(f2,negated_conjecture,(~p)).
fof(f3,plain,($false),inference(resolution,[],[f1,f2])).
"""


def test_tstp_derivation_reports_steps_roles_rule_and_parent_chain():
    """3 statements (2 leaves + 1 inference citing both): step count 3, roles
    {axiom, negated_conjecture, plain}, final step f3 applies 'resolution'
    citing parents f1 and f2 — hand-derived directly from the TSTP text."""
    derivation = parse_tstp_derivation(_TSTP_ONE_INFERENCE)
    assert len(derivation.steps) == 3   # sanity: matches what was written above

    text = explain_proof(derivation)
    assert "The derivation has 3 steps." in text
    assert "Roles present: axiom, negated_conjecture, plain." in text
    assert "The final step f3 applies resolution, tracing back through f1, f2." in text


def test_tstp_derivation_dict_matches_typed_object():
    derivation = parse_tstp_derivation(_TSTP_ONE_INFERENCE)
    assert explain_proof(derivation) == explain_proof(derivation.to_dict())


def test_tstp_multi_level_chain_traces_all_ancestors_breadth_first():
    """f4 <- f3 <- {f1, f2}: a backward walk from f4 must reach every one of
    f3, f1, f2 (not just the immediate parent f3), layer by layer."""
    text_src = """\
fof(f1,axiom,(p)).
fof(f2,axiom,(q)).
fof(f3,plain,(p & q),inference(and_rule,[],[f1,f2])).
fof(f4,plain,($false),inference(final_rule,[],[f3])).
"""
    derivation = parse_tstp_derivation(text_src)
    text = explain_proof(derivation)
    assert "The derivation has 4 steps." in text
    assert "The final step f4 applies final_rule, tracing back through f3, f1, f2." in text


def test_tstp_final_step_without_rule_is_reported_as_a_leaf():
    """A single-step derivation with no inference record (rule=None) must be
    stated honestly as a leaf, never invent a rule name."""
    derivation = TstpDerivation(steps=(
        TstpStep(name="a1", language="fof", role="axiom",
                 formula_text="(p)", formula=P, rule=None, parents=()),
    ))
    text = explain_proof(derivation)
    assert "The derivation has 1 step." in text
    assert "Roles present: axiom." in text
    assert "The final step a1 is a leaf with no inference rule recorded." in text


def test_tstp_empty_derivation_raises_value_error():
    with pytest.raises(ValueError):
        explain_proof(TstpDerivation(steps=()))


def test_tstp_explanation_is_deterministic():
    derivation = parse_tstp_derivation(_TSTP_ONE_INFERENCE)
    assert explain_proof(derivation) == explain_proof(derivation)


# ---------------------------------------------------------------------------
# TweeProof: the same two verbatim, check_twee_proof-verified fixtures
# test_twee.py itself uses (Twee 2.6.1, WSL — see that module's docstring for
# provenance), re-parsed here through the real parser and re-verified again
# below before being explained.
# ---------------------------------------------------------------------------

_TWEE_PREM_1 = [_FOL.parse("∀x (f(f(x)) = x)")]
_TWEE_FIXTURE_1 = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): f(f(X)) = X.

Goal 1 (goal): f(f(f(f(anna)))) = anna.
Proof:
  f(f(f(f(anna))))
= { by axiom 1 (premise_1) }
  f(f(anna))
= { by axiom 1 (premise_1) }
  anna

RESULT: Theorem (the conjecture is true).
"""

_TWEE_PREM_2 = [
    _FOL.parse("∀x ∀y ∀z (mult(mult(x,y),z) = mult(x,mult(y,z)))"),
    _FOL.parse("∀x (mult(ident,x) = x)"),
    _FOL.parse("∀x (mult(inv(x),x) = ident)"),
]
_TWEE_FIXTURE_2 = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_2): mult(ident, X) = X.
Axiom 2 (premise_3): mult(inv(X), X) = ident.
Axiom 3 (premise_1): mult(mult(X, Y), Z) = mult(X, mult(Y, Z)).

Lemma 4: mult(inv(X), mult(X, Y)) = Y.
Proof:
  mult(inv(X), mult(X, Y))
= { by axiom 3 (premise_1) R->L }
  mult(mult(inv(X), X), Y)
= { by axiom 2 (premise_3) }
  mult(ident, Y)
= { by axiom 1 (premise_2) }
  Y

Goal 1 (goal): mult(x, ident) = x.
Proof:
  mult(x, ident)
= { by lemma 4 R->L }
  mult(inv(inv(x)), mult(inv(x), mult(x, ident)))
= { by lemma 4 }
  mult(inv(inv(x)), ident)
= { by axiom 2 (premise_3) R->L }
  mult(inv(inv(x)), mult(inv(x), x))
= { by lemma 4 }
  x

RESULT: Theorem (the conjecture is true).
"""


def test_twee_fixture_1_no_lemma_reports_counts_and_chain():
    proof = parse_twee_proof(_TWEE_FIXTURE_1)
    assert check_twee_proof(proof, _TWEE_PREM_1).ok   # independent oracle

    text = explain_proof(proof)
    assert "The proof uses 1 axiom and 0 lemmas." in text
    assert "The goal (goal) states f(f(f(f(anna)))) = anna." in text
    assert "It rewrites f(f(f(f(anna)))) → f(f(anna)) → anna." in text
    assert "Citations: axiom 1 (premise_1), axiom 1 (premise_1)." in text


def test_twee_fixture_2_with_lemma_counts_match_checker_verified_proof():
    """Differential per the roadmap's test_oracle: the reported axiom/lemma
    counts must equal len(proof.axioms)/len(proof.lemmas) exactly, on a proof
    check_twee_proof itself has already certified sound."""
    proof = parse_twee_proof(_TWEE_FIXTURE_2)
    assert check_twee_proof(proof, _TWEE_PREM_2).ok   # independent oracle

    text = explain_proof(proof)
    assert f"The proof uses {len(proof.axioms)} axioms and {len(proof.lemmas)} lemma." in text
    assert len(proof.axioms) == 3
    assert len(proof.lemmas) == 1
    # The goal's chain cites lemma 4 (both directions) and axiom 2 R->L.
    assert "lemma 4 R->L" in text
    assert "lemma 4," in text or text.count("lemma 4") >= 2
    assert "axiom 2 (premise_3) R->L" in text


def test_twee_proof_dict_matches_typed_object():
    proof = parse_twee_proof(_TWEE_FIXTURE_2)
    assert explain_proof(proof) == explain_proof(proof.to_dict())


def test_twee_explanation_is_deterministic():
    proof = parse_twee_proof(_TWEE_FIXTURE_1)
    assert explain_proof(proof) == explain_proof(proof)


# ---------------------------------------------------------------------------
# Z3Backend's {"kind": "z3_unsat_core", "core": [...]} dict
# ---------------------------------------------------------------------------

def test_z3_unsat_core_lists_terms():
    proof = {"kind": "z3_unsat_core", "core": ["p0", "goal"]}
    text = explain_proof(proof)
    assert "Z3 refutes the goal via an unsat core of 2 tracked terms: p0, goal." in text


def test_z3_unsat_core_empty_core_stated_honestly():
    proof = {"kind": "z3_unsat_core", "core": []}
    text = explain_proof(proof)
    assert text == "Z3 refutes the goal via an empty unsat core."


# ---------------------------------------------------------------------------
# CVC5Backend's {"kind": "cvc5_alethe", "text": ..., "unsat_core": [...]} dict
# ---------------------------------------------------------------------------

def test_cvc5_alethe_reports_line_count_and_unsat_core():
    proof = {
        "kind": "cvc5_alethe",
        "text": "(step t1 (cl) :rule resolution)\n(step t2 (cl) :rule false)\n",
        "unsat_core": ["a", "b"],
    }
    text = explain_proof(proof)
    assert "cvc5 refutes the goal with an Alethe proof of 2 lines." in text
    assert "Its unsat core cites 2 terms: a, b." in text


def test_cvc5_alethe_missing_text_and_empty_core_stated_honestly():
    proof = {"kind": "cvc5_alethe", "text": None, "unsat_core": []}
    text = explain_proof(proof)
    assert text == "cvc5 refutes the goal; no Alethe proof text was recorded. Its unsat core is empty."


# ---------------------------------------------------------------------------
# Dispatch: unambiguous across ALL FIVE real Verdict.proof shapes
# ---------------------------------------------------------------------------

def test_dispatch_is_unambiguous_across_every_real_proof_shape():
    """Feeds one instance of each of the five shapes confirmed (by grep) to
    actually reach Verdict.proof, and checks each is routed to its OWN
    renderer (a distinguishing substring only that branch produces) rather
    than crashing or being misrouted onto another shape's handling."""
    premises, conclusion = _mp_premises_and_conclusion()
    tableau_proof = prove_tableau_detailed(premises, conclusion)
    tstp_derivation = parse_tstp_derivation(_TSTP_ONE_INFERENCE)
    twee_proof = parse_twee_proof(_TWEE_FIXTURE_1)
    z3_core = {"kind": "z3_unsat_core", "core": ["p0"]}
    cvc5_alethe = {"kind": "cvc5_alethe", "text": "(step t1 (cl))\n", "unsat_core": []}

    shapes = [
        (tableau_proof, "tableau proof has"),
        (tableau_proof.to_dict(), "tableau proof has"),
        (tstp_derivation, "derivation has"),
        (tstp_derivation.to_dict(), "derivation has"),
        (twee_proof, "proof uses"),
        (twee_proof.to_dict(), "proof uses"),
        (z3_core, "unsat core"),
        (cvc5_alethe, "Alethe proof"),
    ]
    for proof, marker in shapes:
        text = explain_proof(proof)
        assert marker in text, f"{proof!r} -> {text!r} missing marker {marker!r}"


# ---------------------------------------------------------------------------
# Error contract for unrecognised input
# ---------------------------------------------------------------------------

def test_unrecognised_kind_raises_value_error():
    with pytest.raises(ValueError):
        explain_proof({"kind": "mystery"})


def test_unrecognised_dict_shape_raises_value_error():
    with pytest.raises(ValueError):
        explain_proof({"foo": "bar"})


def test_unsupported_type_raises_type_error():
    with pytest.raises(TypeError):
        explain_proof(42)
