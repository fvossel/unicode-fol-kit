"""Tests for the Twee integration (atp/twee_entailment.py, twee_check.py, twee_backend.py).

Three tiers, matching the kit's convention for external-prover integrations
(see e.g. ``tests/test_vampire_entailment.py``, ``tests/test_cvc5_backend.py``):

* **Offline, no Twee needed**: the equational-fragment gate, TPTP problem
  generation, the term/proof PARSER exercised against VERBATIM stdout text
  captured live on this machine (Twee 2.6.1, WSL — see fixtures below and
  ``atp.twee_entailment``'s module docstring for where each shape came
  from), and the independent CHECKER exercised against those same real
  proofs plus hand-constructed tampered variants (wrong axiom cited, a
  skipped step, a flipped ``R->L``, ...) that must each be rejected for a
  specific, checkable reason.
* **Offline, stubbed runner**: :class:`~atp.twee_backend.TweeBackend`'s
  status mapping, with ``check_entailment_twee_detailed`` monkeypatched so
  the Verdict-construction logic is exercised without a real subprocess.
* **Live, skipped when Twee is not resolvable**
  (``@pytest.mark.skipif(not twee_available(), ...)``): a Theorem whose
  proof is independently verified end to end, a genuine
  CounterSatisfiable, and the group-theory lemma proof (right-identity from
  left-identity + left-inverse + associativity) checked end to end through
  the real backend.

Every offline fixture below (``_FIXTURE_*``) is a REAL captured
``twee --quiet`` stdout, produced by the SAME ``_generate_twee_input`` this
module drives (so the ``premise_<i>``/``goal`` naming lines up exactly with
what a real run against the paired premises/conclusion below each fixture
would produce) — nothing here is invented or guessed.
"""

import dataclasses

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.protocol import ERROR, PROVED, REFUTED, UNKNOWN
from unicode_fol_kit.atp.twee_backend import TweeBackend
from unicode_fol_kit.atp.twee_check import (
    TweeCheckResult, _equation_is_variant, _expected_axiom_equations,
    _flatten_equations, _freshen, _match, _verify_rewrite,
    check_twee_proof, goal_matches_conclusion,
)
from unicode_fol_kit.atp.twee_entailment import (
    TweeChain, TweeCitation, TweeEquation, TweeGoal, TweeLemma, TweeProof,
    _extract_result_status, _generate_twee_input, _is_equational,
    _parse_term, _split_equation, check_entailment_twee_detailed,
    parse_twee_proof, twee_available,
)
from unicode_fol_kit.fol.nodes import Atom, Constant, Function, Number, Variable

_P = MSFLParser()

# ---------------------------------------------------------------------------
# Verbatim fixtures — every one captured live via
# atp.twee_entailment._spawn_twee(_generate_twee_input(premises, conclusion))
# on this machine (Twee 2.6.1, WSL). Paired with the exact premises/
# conclusion (built through the real kit grammar) that produced them.
# ---------------------------------------------------------------------------

# f(f(x)) = x proves f(f(f(f(anna)))) = anna. No lemma.
_PREM_1 = [_P.parse("∀x (f(f(x)) = x)")]
_CONCL_1 = _P.parse("f(f(f(f(anna)))) = anna")
_FIXTURE_1 = """\
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

# Left-group axioms (associativity, left identity, left inverse) prove right
# identity, via one lemma (mult(inv(X), mult(X,Y)) = Y) applied 4 times with
# mixed directions. Axiom numbers deliberately do NOT match premise-list
# order (Twee only lists USED axioms, renumbered locally) — this is exactly
# the case _expected_axiom_equations's premise_<i> naming exists for.
_PREM_2 = [
    _P.parse("∀x ∀y ∀z (mult(mult(x,y),z) = mult(x,mult(y,z)))"),
    _P.parse("∀x (mult(ident,x) = x)"),
    _P.parse("∀x (mult(inv(x),x) = ident)"),
]
_CONCL_2 = _P.parse("∀x (mult(x,ident) = x)")
_FIXTURE_2 = """\
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

# Same group axioms prove inv(inv(x)) = x: a longer (6-step) goal chain
# reusing the SAME lemma 5 times with mixed directions, including a
# same-named-variable citation (axiom 3 also uses X, Y, Z, same letters the
# lemma itself uses) — the exact scenario _freshen exists to make safe.
_PREM_3 = _PREM_2
_CONCL_3 = _P.parse("∀x (inv(inv(x)) = x)")
_FIXTURE_3 = """\
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

Goal 1 (goal): inv(inv(x)) = x.
Proof:
  inv(inv(x))
= { by lemma 4 R->L }
  mult(inv(inv(x)), mult(inv(x), inv(inv(x))))
= { by lemma 4 R->L }
  mult(inv(inv(x)), mult(inv(inv(inv(x))), mult(inv(inv(x)), mult(inv(x), inv(inv(x))))))
= { by lemma 4 }
  mult(inv(inv(x)), mult(inv(inv(inv(x))), inv(inv(x))))
= { by axiom 2 (premise_3) }
  mult(inv(inv(x)), ident)
= { by axiom 2 (premise_3) R->L }
  mult(inv(inv(x)), mult(inv(x), x))
= { by lemma 4 }
  x

RESULT: Theorem (the conjecture is true).
"""

_FIXTURE_COUNTERSAT = "RESULT: CounterSatisfiable (the conjecture is false).\n"
_FIXTURE_GAVEUP = "RESULT: GaveUp (couldn't solve the problem).\n"
_FIXTURE_SATISFIABLE = "RESULT: Satisfiable (the axioms are consistent).\n"


# ---------------------------------------------------------------------------
# Equational fragment gate (offline)
# ---------------------------------------------------------------------------

def test_is_equational_accepts_bare_equation():
    assert _is_equational(_P.parse("f(anna) = anna"))


def test_is_equational_accepts_forall_closed_equation():
    assert _is_equational(_P.parse("∀x (f(x) = x)"))


def test_is_equational_accepts_conjunction_of_equations():
    assert _is_equational(_P.parse("∀x ((f(x) = x) ∧ (g(x) = x))"))


@pytest.mark.parametrize("formula", [
    "P(anna) → Q(anna)",     # implication
    "P(anna) ∨ Q(anna)",     # disjunction
    "¬(anna = anna)",        # negation
    "P(anna)",                # a non-equality predicate
    "∃x (f(x) = x)",          # existential, not universal
])
def test_is_equational_rejects_non_equational_shapes(formula):
    assert not _is_equational(_P.parse(formula))


def test_check_entailment_raises_for_non_equational_premise_naming_it():
    with pytest.raises(NotImplementedError, match="premise 1"):
        check_entailment_twee_detailed([_P.parse("P(anna) → Q(anna)")], _P.parse("anna = anna"))


def test_check_entailment_raises_for_non_equational_conclusion_naming_it():
    with pytest.raises(NotImplementedError, match="conclusion"):
        check_entailment_twee_detailed([_P.parse("anna = anna")], _P.parse("P(anna)"))


def test_check_entailment_raises_before_spawning_any_subprocess():
    # A bogus twee_cmd would blow up immediately if a subprocess were ever
    # spawned — the fragment check must run first and raise before that.
    with pytest.raises(NotImplementedError):
        check_entailment_twee_detailed(
            [_P.parse("P(anna)")], _P.parse("anna = anna"),
            twee_cmd="definitely_not_a_real_twee_xyz")


# ---------------------------------------------------------------------------
# TPTP problem generation (offline)
# ---------------------------------------------------------------------------

def test_generate_twee_input_shape():
    text = _generate_twee_input(_PREM_1, _CONCL_1)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        f"fof(premise_1, axiom, {_PREM_1[0].to_tptp()}).",
        f"fof(goal, conjecture, {_CONCL_1.to_tptp()}).",
    ]


def test_generate_twee_input_multiple_premises_numbered_in_order():
    text = _generate_twee_input(_PREM_2, _CONCL_2)
    assert "fof(premise_1, axiom," in text
    assert "fof(premise_2, axiom," in text
    assert "fof(premise_3, axiom," in text
    assert text.count(", axiom, ") == 3
    assert text.count(", conjecture, ") == 1


# ---------------------------------------------------------------------------
# Term parser (offline)
# ---------------------------------------------------------------------------

def test_parse_term_constant():
    assert _parse_term("anna") == Constant("anna")


def test_parse_term_variable_uppercase():
    assert _parse_term("X") == Variable("X")


def test_parse_term_function_nested():
    assert _parse_term("f(f(anna))") == Function("f", [Function("f", [Constant("anna")])])


def test_parse_term_function_multiple_args_space_after_comma():
    assert _parse_term("mult(inv(X), Y)") == Function("mult", [Function("inv", [Variable("X")]), Variable("Y")])


def test_parse_term_number():
    assert _parse_term("42") == Number(42)


@pytest.mark.parametrize("text", [
    "f(anna",          # unbalanced parens
    "f(anna))",         # trailing token
    "f(,anna)",         # stray comma
    "",                  # empty
])
def test_parse_term_rejects_malformed_text(text):
    with pytest.raises(ValueError):
        _parse_term(text)


def test_split_equation_splits_on_sole_top_level_equals():
    assert _split_equation("f(f(X)) = X") == ("f(f(X))", "X")


def test_split_equation_rejects_text_without_equals():
    with pytest.raises(ValueError):
        _split_equation("f(f(X))")


# ---------------------------------------------------------------------------
# Result-status extraction (offline)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("stdout, expected", [
    (_FIXTURE_1, "Theorem"),
    (_FIXTURE_COUNTERSAT, "CounterSatisfiable"),
    (_FIXTURE_GAVEUP, "GaveUp"),
    (_FIXTURE_SATISFIABLE, "Satisfiable"),
    ("", None),
    ("Error in foo.p: unbound variable X\n", None),
])
def test_extract_result_status(stdout, expected):
    assert _extract_result_status(stdout) == expected


# ---------------------------------------------------------------------------
# Proof parser against VERBATIM captured output (offline)
# ---------------------------------------------------------------------------

def test_parse_proof_none_for_countersatisfiable():
    assert parse_twee_proof(_FIXTURE_COUNTERSAT) is None


def test_parse_proof_none_for_gaveup():
    assert parse_twee_proof(_FIXTURE_GAVEUP) is None


def test_parse_fixture_1_structure():
    proof = parse_twee_proof(_FIXTURE_1)
    assert len(proof.axioms) == 1
    assert proof.axioms[0].number == 1
    assert proof.axioms[0].name == "premise_1"
    assert proof.axioms[0].equation.lhs == Function("f", [Function("f", [Variable("X")])])
    assert proof.axioms[0].equation.rhs == Variable("X")
    assert len(proof.lemmas) == 0
    assert proof.goal.name == "goal"
    assert proof.goal.equation.lhs == _parse_term("f(f(f(f(anna))))")
    assert proof.goal.equation.rhs == Constant("anna")
    assert len(proof.goal.chain.terms) == 3
    assert len(proof.goal.chain.citations) == 2
    for c in proof.goal.chain.citations:
        assert c.kind == "axiom" and c.number == 1 and c.name == "premise_1" and not c.reversed


def test_parse_fixture_2_structure_axiom_numbering_and_names():
    proof = parse_twee_proof(_FIXTURE_2)
    # Axiom NUMBERS are a local 1..3 indexing scheme, unrelated to the
    # premise_<i> NAMES, which reflect original premise-list position.
    by_number = {a.number: a.name for a in proof.axioms}
    assert by_number == {1: "premise_2", 2: "premise_3", 3: "premise_1"}
    assert len(proof.lemmas) == 1
    lemma = proof.lemmas[0]
    assert lemma.number == 4
    assert lemma.equation.lhs == _parse_term("mult(inv(X), mult(X, Y))")
    assert lemma.equation.rhs == Variable("Y")
    # First lemma step cites axiom 3 (premise_1, i.e. associativity) R->L.
    first_citation = lemma.chain.citations[0]
    assert first_citation == TweeCitation("axiom", 3, "premise_1", True)
    # Goal cites: lemma 4 (R->L), lemma 4 (forward), axiom 2 (R->L), lemma 4
    # (forward) — mixed axiom/lemma citations, mixed directions.
    goal_kinds = [(c.kind, c.number, c.name, c.reversed) for c in proof.goal.chain.citations]
    assert goal_kinds == [
        ("lemma", 4, None, True),
        ("lemma", 4, None, False),
        ("axiom", 2, "premise_3", True),
        ("lemma", 4, None, False),
    ]


def test_parse_fixture_3_six_step_chain_reusing_one_lemma():
    proof = parse_twee_proof(_FIXTURE_3)
    assert len(proof.goal.chain.terms) == 7
    assert len(proof.goal.chain.citations) == 6
    kinds = [(c.kind, c.number, c.reversed) for c in proof.goal.chain.citations]
    assert kinds == [
        ("lemma", 4, True), ("lemma", 4, True), ("lemma", 4, False),
        ("axiom", 2, False), ("axiom", 2, True), ("lemma", 4, False),
    ]


# ---------------------------------------------------------------------------
# Proof parser: malformed Theorem text raises ValueError (hand-corrupted
# variants of _FIXTURE_1, never a guess)
# ---------------------------------------------------------------------------

def test_parse_proof_rejects_missing_banner():
    corrupted = _FIXTURE_1.replace("The conjecture is true! Here is a proof.\n\n", "")
    with pytest.raises(ValueError, match="banner"):
        parse_twee_proof(corrupted)


def test_parse_proof_rejects_missing_proof_marker_after_goal():
    corrupted = _FIXTURE_1.replace("Proof:\n", "")
    with pytest.raises(ValueError, match="Proof:"):
        parse_twee_proof(corrupted)


def test_parse_proof_rejects_axiom_citation_without_name():
    corrupted = _FIXTURE_1.replace("{ by axiom 1 (premise_1) }", "{ by axiom 1 }")
    with pytest.raises(ValueError, match="missing its"):
        parse_twee_proof(corrupted)


def test_parse_proof_rejects_theorem_with_no_goal_block():
    corrupted = "The conjecture is true! Here is a proof.\n\nRESULT: Theorem (the conjecture is true).\n"
    with pytest.raises(ValueError, match="no Goal block"):
        parse_twee_proof(corrupted)


def test_parse_proof_rejects_unrecognised_header_line():
    corrupted = _FIXTURE_1.replace(
        "Axiom 1 (premise_1): f(f(X)) = X.\n", "Axiom 1 (premise_1): f(f(X)) = X.\nWibble!\n")
    with pytest.raises(ValueError):
        parse_twee_proof(corrupted)


# ---------------------------------------------------------------------------
# _match / _verify_rewrite core (offline, hand-derived)
# ---------------------------------------------------------------------------

def test_match_binds_pattern_variable_to_ground_term():
    subst = _match(Variable("X"), Constant("a"), {})
    assert subst == {"X": Constant("a")}


def test_match_rejects_constant_mismatch():
    assert _match(Constant("a"), Constant("b"), {}) is None


def test_match_requires_consistent_repeated_variable():
    # p(X, X) matching p(a, a): consistent -> succeeds.
    pattern = Function("p", [Variable("X"), Variable("X")])
    assert _match(pattern, Function("p", [Constant("a"), Constant("a")]), {}) == {"X": Constant("a")}
    # p(X, X) matching p(a, b): inconsistent -> fails.
    assert _match(pattern, Function("p", [Constant("a"), Constant("b")]), {}) is None


def test_verify_rewrite_direct_top_level():
    # axiom f(X) = g(X); f(a) -[fwd]-> g(a).
    assert _verify_rewrite(Function("f", [Constant("a")]), Function("g", [Constant("a")]),
                           Function("f", [Variable("X")]), Function("g", [Variable("X")]))


def test_verify_rewrite_nested_subterm():
    # h(f(a), b) -[fwd]-> h(g(a), b): redex is the NESTED f(a), not the root.
    term1 = Function("h", [Function("f", [Constant("a")]), Constant("b")])
    term2 = Function("h", [Function("g", [Constant("a")]), Constant("b")])
    assert _verify_rewrite(term1, term2, Function("f", [Variable("X")]), Function("g", [Variable("X")]))


def test_verify_rewrite_rejects_inconsistent_result():
    # Same axiom, but term2's argument does not match term1's — no valid redex.
    term1 = Function("f", [Constant("a")])
    term2 = Function("g", [Constant("b")])   # should have been g(a)
    assert not _verify_rewrite(term1, term2, Function("f", [Variable("X")]), Function("g", [Variable("X")]))


def test_verify_rewrite_reverse_direction_with_variable_only_on_to_side():
    # Hand-derived asymmetric case (mirrors Lemma 4's own R->L steps):
    # axiom p(X, Y) = q(Y) ["from"=q(Y) i.e. R->L is being applied here: the
    # cited equation's "from" side is q(Y), "to" side is p(X, Y) — X is NOT
    # determined by matching "from" alone, since X does not occur in q(Y)].
    from_pattern = Function("q", [Variable("Y")])
    to_pattern = Function("p", [Variable("X"), Variable("Y")])
    term1 = Function("q", [Constant("c")])
    # X is free to be ANY term; here the prover chose the constant "d".
    term2 = Function("p", [Constant("d"), Constant("c")])
    assert _verify_rewrite(term1, term2, from_pattern, to_pattern)
    # But Y must stay consistent: q(c) cannot become p(d, e) (e != c).
    bad_term2 = Function("p", [Constant("d"), Constant("e")])
    assert not _verify_rewrite(term1, bad_term2, from_pattern, to_pattern)


def test_verify_rewrite_does_not_infinite_loop_on_shared_variable_names():
    # Regression test for the collision _freshen fixes: term1/term2 use a
    # variable literally named "X" (as if inside another equation's own
    # chain), and the CITED axiom ALSO uses "X" as ITS OWN, unrelated,
    # rewrite variable. Without freshening this recurses forever inside
    # apply_subst (X -> X). axiom: f(X) = g(X); term1 = h(f(X), b) using a
    # DIFFERENT "X" that must stay untouched.
    term1 = Function("h", [Function("f", [Variable("X")]), Constant("b")])
    term2 = Function("h", [Function("g", [Variable("X")]), Constant("b")])
    assert _verify_rewrite(term1, term2, Function("f", [Variable("X")]), Function("g", [Variable("X")]))


def test_freshen_renames_all_variables_with_a_disjoint_prefix():
    term = Function("f", [Variable("X"), Function("g", [Variable("Y")]), Constant("a")])
    fresh = _freshen(term, "#")
    assert fresh == Function("f", [Variable("#X"), Function("g", [Variable("#Y")]), Constant("a")])


# ---------------------------------------------------------------------------
# _flatten_equations / _expected_axiom_equations / _equation_is_variant
# (offline, hand-derived)
# ---------------------------------------------------------------------------

def test_flatten_equations_single():
    lhs, rhs = _P.parse("f(anna) = anna").args
    assert _flatten_equations(_P.parse("f(anna) = anna")) == [(lhs, rhs)]


def test_flatten_equations_forall_and_conjunction_left_to_right():
    node = _P.parse("∀x ((f(x) = x) ∧ (g(x) = x))")
    pairs = _flatten_equations(node)
    assert len(pairs) == 2
    assert pairs[0][0] == Function("f", [Variable("x")])
    assert pairs[1][0] == Function("g", [Variable("x")])


def test_expected_axiom_equations_naming_scheme():
    mapping = _expected_axiom_equations(_PREM_2)
    assert set(mapping) == {"premise_1", "premise_2", "premise_3"}


def test_expected_axiom_equations_suffixes_extra_conjuncts():
    premises = [_P.parse("∀x ((f(x) = x) ∧ (g(x) = x))"), _P.parse("h(anna) = anna")]
    mapping = _expected_axiom_equations(premises)
    assert set(mapping) == {"premise_1", "premise_1_1", "premise_2"}


def test_equation_is_variant_ignores_variable_names():
    expected = (Function("f", [Variable("x")]), Variable("x"))
    actual = (Function("f", [Variable("X")]), Variable("X"))
    assert _equation_is_variant(expected, actual)


def test_equation_is_variant_rejects_structural_mismatch():
    expected = (Function("f", [Variable("x")]), Variable("x"))
    actual = (Function("f", [Constant("a")]), Constant("b"))
    assert not _equation_is_variant(expected, actual)


def test_equation_is_variant_rejects_inconsistent_repeated_variable():
    # f(x, x) = x  vs  f(X, Y) = X: x maps to both X and Y -> not injective.
    expected = (Function("f", [Variable("x"), Variable("x")]), Variable("x"))
    actual = (Function("f", [Variable("X"), Variable("Y")]), Variable("X"))
    assert not _equation_is_variant(expected, actual)


# ---------------------------------------------------------------------------
# check_twee_proof against real proofs (offline, from the verbatim fixtures)
# ---------------------------------------------------------------------------

def test_check_twee_proof_accepts_fixture_1():
    proof = parse_twee_proof(_FIXTURE_1)
    assert check_twee_proof(proof, _PREM_1) == TweeCheckResult(True)


def test_check_twee_proof_accepts_fixture_2_with_lemma():
    proof = parse_twee_proof(_FIXTURE_2)
    result = check_twee_proof(proof, _PREM_2)
    assert result.ok, result.error


def test_check_twee_proof_accepts_fixture_3_reused_lemma_mixed_directions():
    proof = parse_twee_proof(_FIXTURE_3)
    result = check_twee_proof(proof, _PREM_3)
    assert result.ok, result.error


def test_goal_matches_conclusion_true_for_fixture_1():
    proof = parse_twee_proof(_FIXTURE_1)
    assert goal_matches_conclusion(proof, _CONCL_1)


def test_goal_matches_conclusion_true_for_fixture_2():
    proof = parse_twee_proof(_FIXTURE_2)
    assert goal_matches_conclusion(proof, _CONCL_2)


def test_goal_matches_conclusion_false_for_wrong_conclusion():
    proof = parse_twee_proof(_FIXTURE_1)
    wrong = _P.parse("f(f(f(anna))) = anna")   # 3 applications, not 4
    assert not goal_matches_conclusion(proof, wrong)


# ---------------------------------------------------------------------------
# check_twee_proof REJECTS tampered variants of a real proof (offline,
# hand-derived; each tamper isolates exactly one failure mode)
# ---------------------------------------------------------------------------

def _real_proof_and_premises():
    return parse_twee_proof(_FIXTURE_2), _PREM_2


def test_check_twee_proof_rejects_axiom_naming_a_premise_not_given():
    proof, premises = _real_proof_and_premises()
    bad_axiom = dataclasses.replace(proof.axioms[0], name="premise_99")
    bad_proof = dataclasses.replace(proof, axioms=(bad_axiom,) + proof.axioms[1:])
    result = check_twee_proof(bad_proof, premises)
    assert not result.ok
    assert "premise_99" in result.error


def test_check_twee_proof_rejects_axiom_restatement_not_matching_given_premise():
    proof, premises = _real_proof_and_premises()
    # Restate axiom 1 (premise_2: mult(ident,X)=X) as something else entirely.
    bad_equation = TweeEquation(Function("mult", [Variable("X"), Variable("X")]), Variable("X"))
    bad_axiom = dataclasses.replace(proof.axioms[0], equation=bad_equation)
    bad_proof = dataclasses.replace(proof, axioms=(bad_axiom,) + proof.axioms[1:])
    result = check_twee_proof(bad_proof, premises)
    assert not result.ok
    assert "not alpha-equivalent" in result.error


def test_check_twee_proof_rejects_wrong_direction_flag():
    proof, premises = _real_proof_and_premises()
    citations = proof.goal.chain.citations
    flipped = dataclasses.replace(citations[0], reversed=not citations[0].reversed)
    bad_chain = dataclasses.replace(proof.goal.chain, citations=(flipped,) + citations[1:])
    bad_proof = dataclasses.replace(proof, goal=dataclasses.replace(proof.goal, chain=bad_chain))
    result = check_twee_proof(bad_proof, premises)
    assert not result.ok
    assert "not a valid single-rewrite instance" in result.error


def test_check_twee_proof_rejects_skipped_step():
    proof, premises = _real_proof_and_premises()
    chain = proof.goal.chain
    assert len(chain.terms) >= 3
    skipped_chain = TweeChain((chain.terms[0],) + chain.terms[2:], chain.citations[1:])
    bad_proof = dataclasses.replace(proof, goal=dataclasses.replace(proof.goal, chain=skipped_chain))
    result = check_twee_proof(bad_proof, premises)
    assert not result.ok


def test_check_twee_proof_rejects_wrong_axiom_number_citation():
    proof, premises = _real_proof_and_premises()
    citations = proof.goal.chain.citations
    bad = dataclasses.replace(citations[0], number=citations[0].number + 1000)
    bad_chain = dataclasses.replace(proof.goal.chain, citations=(bad,) + citations[1:])
    bad_proof = dataclasses.replace(proof, goal=dataclasses.replace(proof.goal, chain=bad_chain))
    result = check_twee_proof(bad_proof, premises)
    assert not result.ok
    assert "not an earlier proven lemma" in result.error


def test_check_twee_proof_rejects_chain_not_starting_at_stated_lhs():
    proof, premises = _real_proof_and_premises()
    lemma = proof.lemmas[0]
    bad_chain = dataclasses.replace(lemma.chain, terms=(Constant("bogus"),) + lemma.chain.terms[1:])
    bad_lemma = dataclasses.replace(lemma, chain=bad_chain)
    bad_proof = dataclasses.replace(proof, lemmas=(bad_lemma,))
    result = check_twee_proof(bad_proof, premises)
    assert not result.ok
    assert "does not start" in result.error


def test_check_twee_proof_rejects_forward_lemma_citation():
    # A lemma cannot cite ANOTHER lemma with an equal-or-greater number
    # (would be a forward/self reference). Fabricate a second, later lemma
    # that cites itself.
    proof, premises = _real_proof_and_premises()
    lemma = proof.lemmas[0]
    self_citation = TweeCitation("lemma", lemma.number, None, False)
    fake_chain = TweeChain((lemma.equation.lhs, lemma.equation.rhs), (self_citation,))
    fake_lemma = dataclasses.replace(lemma, chain=fake_chain)
    bad_proof = dataclasses.replace(proof, lemmas=(fake_lemma,))
    result = check_twee_proof(bad_proof, premises)
    assert not result.ok
    assert "not an earlier proven lemma" in result.error


def test_check_twee_proof_rejects_duplicate_axiom_number():
    proof, premises = _real_proof_and_premises()
    dup = dataclasses.replace(proof.axioms[1], number=proof.axioms[0].number)
    bad_proof = dataclasses.replace(proof, axioms=(proof.axioms[0], dup) + proof.axioms[2:])
    result = check_twee_proof(bad_proof, premises)
    assert not result.ok
    assert "restated more than once" in result.error


# ---------------------------------------------------------------------------
# TweeBackend, offline, with the runner stubbed (monkeypatch) — status
# mapping only; check_twee_proof/goal_matches_conclusion run for REAL against
# a minimal, hand-built, genuinely valid TweeProof (a reflexivity proof).
# ---------------------------------------------------------------------------

def _trivial_verified_result():
    """A minimal, genuinely-valid TweeProof: no axioms/lemmas needed, goal a=a."""
    goal = TweeGoal(1, "goal", TweeEquation(Constant("a"), Constant("a")),
                    TweeChain((Constant("a"),), ()))
    proof = TweeProof((), (), goal)
    return {"status": "Theorem", "raw_output": "stub", "proof": proof, "timed_out": False}


def test_backend_unsupported_fragment(monkeypatch):
    backend = TweeBackend()
    v = backend.decide(_P.parse("P(anna)"), [])
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"


def test_backend_proved_when_status_theorem_and_verified(monkeypatch):
    backend = TweeBackend()
    monkeypatch.setattr("unicode_fol_kit.atp.twee_entailment.check_entailment_twee_detailed",
                        lambda *a, **k: _trivial_verified_result())
    v = backend.decide(Atom("=", [Constant("a"), Constant("a")]), [])
    assert v.status == PROVED
    assert v.proof is not None
    assert v.detail is not None and "verified" in v.detail


def test_backend_error_when_theorem_but_check_twee_proof_fails(monkeypatch):
    backend = TweeBackend()
    monkeypatch.setattr("unicode_fol_kit.atp.twee_entailment.check_entailment_twee_detailed",
                        lambda *a, **k: _trivial_verified_result())
    monkeypatch.setattr("unicode_fol_kit.atp.twee_check.check_twee_proof",
                        lambda proof, axioms: TweeCheckResult(False, "fabricated failure"))
    v = backend.decide(Atom("=", [Constant("a"), Constant("a")]), [])
    assert v.status == ERROR
    assert v.reason == "infra"
    assert "fabricated failure" in v.detail


def test_backend_error_when_theorem_but_goal_does_not_match_conclusion(monkeypatch):
    backend = TweeBackend()
    monkeypatch.setattr("unicode_fol_kit.atp.twee_entailment.check_entailment_twee_detailed",
                        lambda *a, **k: _trivial_verified_result())
    # Ask for a DIFFERENT conclusion than the stubbed proof's goal (a=a).
    v = backend.decide(Atom("=", [Constant("b"), Constant("b")]), [])
    assert v.status == ERROR
    assert v.reason == "infra"
    assert "does not restate" in v.detail


def test_backend_refuted_on_countersatisfiable(monkeypatch):
    backend = TweeBackend()
    monkeypatch.setattr("unicode_fol_kit.atp.twee_entailment.check_entailment_twee_detailed",
                        lambda *a, **k: {"status": "CounterSatisfiable", "raw_output": "stub",
                                         "proof": None, "timed_out": False})
    v = backend.decide(Atom("=", [Constant("a"), Constant("b")]), [])
    assert v.status == REFUTED


def test_backend_unknown_timeout(monkeypatch):
    backend = TweeBackend()
    monkeypatch.setattr("unicode_fol_kit.atp.twee_entailment.check_entailment_twee_detailed",
                        lambda *a, **k: {"status": "Unknown", "raw_output": "", "proof": None,
                                         "timed_out": True})
    v = backend.decide(Atom("=", [Constant("a"), Constant("b")]), [])
    assert v.status == UNKNOWN
    assert v.reason == "timeout"


def test_backend_unknown_incomplete_for_gaveup(monkeypatch):
    backend = TweeBackend()
    monkeypatch.setattr("unicode_fol_kit.atp.twee_entailment.check_entailment_twee_detailed",
                        lambda *a, **k: {"status": "GaveUp", "raw_output": _FIXTURE_GAVEUP,
                                         "proof": None, "timed_out": False})
    v = backend.decide(Atom("=", [Constant("a"), Constant("b")]), [])
    assert v.status == UNKNOWN
    assert v.reason == "incomplete"
    assert "GaveUp" in v.detail


def test_backend_wraps_notimplementederror_from_runner(monkeypatch):
    # Belt-and-braces: even if the fragment check somehow only raised deep
    # inside the runner (not before backend.decide's own call), it must
    # still come back UNKNOWN/unsupported, not propagate.
    backend = TweeBackend()

    def _raise(*a, **k):
        raise NotImplementedError("fake unsupported node")
    monkeypatch.setattr("unicode_fol_kit.atp.twee_entailment.check_entailment_twee_detailed", _raise)
    v = backend.decide(Atom("=", [Constant("a"), Constant("a")]), [])
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"


def test_backend_name_logics_external():
    backend = TweeBackend()
    assert backend.name == "twee"
    assert backend.logics == frozenset({"fol"})
    assert backend.external is True


# ---------------------------------------------------------------------------
# Live — only when a Twee binary is actually resolvable (WSL by default)
# ---------------------------------------------------------------------------

_TWEE_AVAILABLE = twee_available()


@pytest.mark.skipif(not _TWEE_AVAILABLE, reason="no Twee binary reachable via WSL")
def test_live_theorem_end_to_end_verified():
    result = check_entailment_twee_detailed(_PREM_1, _CONCL_1, timeout=30)
    assert result["status"] == "Theorem"
    check_result = check_twee_proof(result["proof"], _PREM_1)
    assert check_result.ok, check_result.error
    assert goal_matches_conclusion(result["proof"], _CONCL_1)


@pytest.mark.skipif(not _TWEE_AVAILABLE, reason="no Twee binary reachable via WSL")
def test_live_countersatisfiable():
    # f(f(f(anna))) = anna does NOT follow from f(f(x))=x in general.
    bad_conclusion = _P.parse("f(f(f(anna))) = anna")
    result = check_entailment_twee_detailed(_PREM_1, bad_conclusion, timeout=30)
    assert result["status"] == "CounterSatisfiable"
    assert result["proof"] is None


@pytest.mark.skipif(not _TWEE_AVAILABLE, reason="no Twee binary reachable via WSL")
def test_live_group_theory_lemma_proof_end_to_end():
    result = check_entailment_twee_detailed(_PREM_2, _CONCL_2, timeout=30)
    assert result["status"] == "Theorem"
    assert len(result["proof"].lemmas) >= 1
    check_result = check_twee_proof(result["proof"], _PREM_2)
    assert check_result.ok, check_result.error
    assert goal_matches_conclusion(result["proof"], _CONCL_2)


@pytest.mark.skipif(not _TWEE_AVAILABLE, reason="no Twee binary reachable via WSL")
def test_live_backend_proved():
    backend = TweeBackend()
    v = backend.decide(_CONCL_1, _PREM_1, timeout=30000)
    assert v.status == PROVED
    assert v.proof is not None
    assert v.wall_time > 0


@pytest.mark.skipif(not _TWEE_AVAILABLE, reason="no Twee binary reachable via WSL")
def test_live_backend_refuted():
    backend = TweeBackend()
    bad_conclusion = _P.parse("f(f(f(anna))) = anna")
    v = backend.decide(bad_conclusion, _PREM_1, timeout=30000)
    assert v.status == REFUTED


@pytest.mark.skipif(not _TWEE_AVAILABLE, reason="no Twee binary reachable via WSL")
def test_live_subprocess_timeout_reports_unknown_timeout():
    result = check_entailment_twee_detailed(_PREM_1, _CONCL_1, timeout=0)
    assert result["status"] == "Unknown"
    assert result["timed_out"] is True


@pytest.mark.skipif(not _TWEE_AVAILABLE, reason="no Twee binary reachable via WSL")
def test_live_ascii_sanitisation_round_trip():
    """A REAL Twee run (through WSL), on a problem using both a non-ASCII
    constant and a digit-leading one, with the proof and raw output
    reverse-mapped back to the ORIGINAL kit-level names — the strongest R5
    evidence this suite can offer for the TPTP Hinweg+Rückweg through the
    equational fragment: an actual external prover, not the kit's own
    reader.
    """
    premise = [_P.parse("∀x (mult(świątek, x) = x)")]
    conclusion = _P.parse("mult(świątek, 2008wins) = 2008wins")
    result = check_entailment_twee_detailed(premise, conclusion, timeout=30)
    assert result["status"] == "Theorem"
    proof = result["proof"]
    assert proof is not None
    assert "świątek" in str(proof.goal.equation.lhs)
    assert "2008wins" in str(proof.goal.equation.rhs)
    # the sanitised tokens must not leak through anywhere in the structured
    # proof or in the free-text raw output.
    assert "u015b" not in str(proof.to_dict())
    assert "u015b" not in result["raw_output"]
    assert "świątek" in result["raw_output"]
    assert "2008wins" in result["raw_output"]
    check_result = check_twee_proof(proof, premise)
    assert check_result.ok, check_result.error
    assert goal_matches_conclusion(proof, conclusion)


def test_goal_match_rejects_non_injective_variable_collapse():
    """Adversarial-review soundness regression: a proof of the GROUND fact
    f(a) = g(a) must never certify the strictly stronger ∀X ∀Y f(X) = g(Y)
    — matching both conclusion variables onto the SAME Skolem term is a
    non-injective binding, which Skolemization of distinct universals can
    never produce. The internal chain is genuinely valid (so
    check_twee_proof accepts it); goal_matches_conclusion must refuse."""
    from unicode_fol_kit import MSFLParser
    from unicode_fol_kit.fol.nodes import Atom, Constant, Function
    from unicode_fol_kit.atp.twee_check import (
        check_twee_proof, goal_matches_conclusion)
    from unicode_fol_kit.atp.twee_entailment import (
        TweeAxiom, TweeChain, TweeCitation, TweeEquation, TweeGoal, TweeProof)

    a = Constant("alpha")
    f_a = Function("f", (a,))
    g_a = Function("g", (a,))
    premise = Atom("=", (f_a, g_a))
    proof = TweeProof(
        axioms=(TweeAxiom(1, "premise_1", TweeEquation(f_a, g_a)),),
        lemmas=(),
        goal=TweeGoal(1, "goal", TweeEquation(f_a, g_a),
                      TweeChain(terms=(f_a, g_a),
                                citations=(TweeCitation("axiom", 1,
                                                        "premise_1"),))),
    )
    assert check_twee_proof(proof, [premise]).ok       # the chain IS valid
    weaker_claim = MSFLParser().parse("∀x ∀y (f(x) = g(y))")
    assert goal_matches_conclusion(proof, weaker_claim) is False
    # The honest conclusion still matches.
    assert goal_matches_conclusion(proof, premise) is True
