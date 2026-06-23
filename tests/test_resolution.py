"""Tests for the first-order resolution prover (unicode_fol_kit.atp.resolution).

Each entailment/validity claim is checked against a hand-derived oracle and,
where the input is propositional, cross-checked against the existing Z3 validity
procedure ``is_valid`` so resolution and Z3 must agree. The non-entailment cases
guard soundness: the prover must NOT report a non-theorem as proved, and a Skolem
constant from ``∃x P(x)`` must not unify with the named constant ``a``.
"""

from functools import reduce

from unicode_fol_kit import MSFLParser, is_valid
from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Constant, Variable,
)
from unicode_fol_kit.atp.resolution import (
    to_clauses, prove, is_valid_resolution, refute,
)

P = MSFLParser()


def parse(s: str):
    """Parse a Unicode FOL string into an AST node."""
    return P.parse(s)


def big_implication(premises, conclusion):
    """Build (premise1 ∧ premise2 ∧ …) → conclusion as nested And/Implies."""
    if not premises:
        return conclusion
    antecedent = reduce(And, premises)
    return Implies(antecedent, conclusion)


# ---------------------------------------------------------------------------
# Propositional / quantifier-free entailment (hand oracles)
# ---------------------------------------------------------------------------

def test_modus_ponens():
    premises = [parse("P → Q"), parse("P")]
    assert prove(premises, parse("Q")) is True


def test_modus_tollens():
    premises = [parse("P → Q"), parse("¬Q")]
    assert prove(premises, parse("¬P")) is True


def test_disjunctive_syllogism():
    premises = [parse("P ∨ Q"), parse("¬P")]
    assert prove(premises, parse("Q")) is True


def test_hypothetical_syllogism():
    premises = [parse("P → Q"), parse("Q → R")]
    assert prove(premises, parse("P → R")) is True


# ---------------------------------------------------------------------------
# First-order entailment (hand oracles)
# ---------------------------------------------------------------------------

def test_socrates():
    premises = [parse("∀x (Human(x) → Mortal(x))"), parse("Human(socrates)")]
    assert prove(premises, parse("Mortal(socrates)")) is True


def test_universal_instantiation():
    # ∀x P(x) ⊨ P(a). 'a' is a single letter, so build the constant explicitly.
    premises = [parse("∀x P(x)")]
    conclusion = Atom("P", [Constant("a")])
    assert prove(premises, conclusion) is True


def test_symmetry_of_relation():
    premises = [parse("∀x ∀y (R(x,y) → R(y,x))"), parse("R(a,b)")]
    assert prove(premises, parse("R(b,a)")) is True


def test_transitivity_chain():
    premises = [
        parse("∀x ∀y ∀z ((R(x,y) ∧ R(y,z)) → R(x,z))"),
        parse("R(a,b)"),
        parse("R(b,c)"),
    ]
    assert prove(premises, parse("R(a,c)")) is True


def test_existential_generalization():
    # P(a) ⊨ ∃x P(x).
    premises = [parse("P(a)")]
    assert prove(premises, parse("∃x P(x)")) is True


def test_barber_contradiction():
    # An inconsistent premise set entails anything (here an arbitrary atom).
    premises = [parse("∀x (Shaves(barber, x) ↔ ¬Shaves(x, x))")]
    assert prove(premises, parse("Q")) is True


# ---------------------------------------------------------------------------
# NON-entailment (soundness guards: must be False)
# ---------------------------------------------------------------------------

def test_non_entailment_socrates_without_rule():
    # Human(socrates) alone does NOT entail Mortal(socrates).
    premises = [parse("Human(socrates)")]
    assert prove(premises, parse("Mortal(socrates)")) is False


def test_existential_does_not_instantiate_named_constant():
    # ∃x P(x) ⊭ P(a): the Skolem constant must not unify with the constant a.
    premises = [parse("∃x P(x)")]
    conclusion = Atom("P", [Constant("a")])
    assert prove(premises, conclusion) is False


def test_non_entailment_propositional():
    # P does not entail Q.
    assert prove([parse("P")], parse("Q")) is False


def test_affirming_the_consequent_is_invalid():
    # (P → Q), Q ⊭ P.
    premises = [parse("P → Q"), parse("Q")]
    assert prove(premises, parse("P")) is False


# ---------------------------------------------------------------------------
# Propositional validity vs Z3
# ---------------------------------------------------------------------------

def test_validity_against_z3():
    formulas = [
        "P ∨ ¬P",
        "(P → Q) ∨ (Q → P)",
        "P → (Q → P)",
        "¬(P ∧ ¬P)",
        "(P ↔ Q) ↔ (Q ↔ P)",
        "((P → Q) ∧ P) → Q",          # modus ponens as a tautology
        "(P ∧ Q) → P",
        "P → (P ∨ Q)",
        "P ∧ ¬P",                      # contradiction: NOT valid
        "P → Q",                       # contingent: NOT valid
        "P ↔ ¬P",                      # contradiction: NOT valid
    ]
    for s in formulas:
        f = parse(s)
        assert is_valid_resolution(f) == is_valid(f), s


# ---------------------------------------------------------------------------
# Propositional entailment vs Z3
# ---------------------------------------------------------------------------

def test_entailment_against_z3():
    cases = [
        (["P → Q", "P"], "Q"),                 # modus ponens (entails)
        (["P → Q", "¬Q"], "¬P"),               # modus tollens (entails)
        (["P ∨ Q", "¬P"], "Q"),                # disjunctive syllogism (entails)
        (["P → Q", "Q → R"], "P → R"),         # hypothetical syllogism (entails)
        (["P"], "Q"),                          # non-entailment
        (["P → Q", "Q"], "P"),                 # affirming consequent (non-entailment)
        (["P ∨ Q"], "P"),                      # non-entailment
        (["P ∧ Q"], "P"),                      # entails
        (["P", "¬P"], "Q"),                    # ex falso (entails)
    ]
    for prem_strs, concl_str in cases:
        premises = [parse(s) for s in prem_strs]
        conclusion = parse(concl_str)
        big = big_implication(premises, conclusion)
        assert prove(premises, conclusion) == is_valid(big), (prem_strs, concl_str)


# ---------------------------------------------------------------------------
# Clausal form and the empty clause
# ---------------------------------------------------------------------------

def test_to_clauses_shape():
    # P ∧ Q → two unit clauses {P}, {Q}.
    clauses = to_clauses(parse("P ∧ Q"))
    assert clauses == {frozenset([Atom("P", [])]), frozenset([Atom("Q", [])])}


def test_to_clauses_disjunction_single_clause():
    # P ∨ Q → one clause {P, Q}.
    clauses = to_clauses(parse("P ∨ Q"))
    assert clauses == {frozenset([Atom("P", []), Atom("Q", [])])}


def test_refute_contradiction():
    # Clauses for (P ∧ ¬P): {P} and {¬P} resolve to the empty clause.
    clauses = to_clauses(parse("P ∧ ¬P"))
    assert refute(clauses) is True


def test_refute_satisfiable_is_false():
    # A single satisfiable unit clause cannot be refuted.
    clauses = to_clauses(parse("P"))
    assert refute(clauses) is False


def test_empty_clause_directly_refutable():
    # A clause set containing the empty clause is unsatisfiable by definition.
    assert refute({frozenset()}) is True


# ---------------------------------------------------------------------------
# is_valid_resolution direct checks
# ---------------------------------------------------------------------------

def test_is_valid_resolution_tautology():
    assert is_valid_resolution(parse("P ∨ ¬P")) is True


def test_is_valid_resolution_fo_tautology():
    # (∀x P(x)) → P(a) is valid.
    f = Implies(parse("∀x P(x)"), Atom("P", [Constant("a")]))
    assert is_valid_resolution(f) is True


def test_is_valid_resolution_contingent_is_false():
    assert is_valid_resolution(parse("P → Q")) is False


# ---------------------------------------------------------------------------
# Standardizing apart actually matters (soundness)
# ---------------------------------------------------------------------------

def test_standardize_apart_clashing_variable_names():
    # Both premises use bound variable x; entailment must still go through
    # because the clauses are renamed apart before resolving.
    premises = [parse("∀x (A(x) → B(x))"), parse("∀x (B(x) → C(x))")]
    assert prove(premises, parse("∀x (A(x) → C(x))")) is True


# ---------------------------------------------------------------------------
# Adversarial soundness regressions (each guards a fixed soundness bug)
# ---------------------------------------------------------------------------

def test_skolem_constants_from_distinct_sources_must_not_collide():
    # ∃x P(x) ⊭ ∀y P(y): "something is P" does NOT entail "everything is P".
    # The premise skolemises to a constant and the negated conclusion
    # (¬∀y P(y) = ∃y ¬P(y)) also skolemises to a constant; if the two Skolem
    # constants were both named 'sk0' they would spuriously resolve to the empty
    # clause. They must be renamed apart, so this is a NON-entailment.
    assert prove([parse("∃x P(x)")], parse("∀y P(y)")) is False
    # Z3 agrees it is not valid.
    assert is_valid(Implies(parse("∃x P(x)"), parse("∀y P(y)"))) is False


def test_existential_entails_existential():
    # ∃x P(x) ⊨ ∃y P(y) — a true entailment that must still go through after the
    # Skolem-symbols of the two sources are renamed apart.
    assert prove([parse("∃x P(x)")], parse("∃y P(y)")) is True


def test_free_variable_under_negation_is_not_universal():
    # (P(x) → ∀y P(y)) is NOT valid: under negation the free x becomes an
    # existential witness (a Skolem FUNCTION of the inner universal), so the
    # occurs-check blocks the otherwise-spurious refutation. Resolution must
    # agree with Z3 that this is invalid.
    f = parse("P(x) → ∀y P(y)")
    assert is_valid(f) is False
    assert is_valid_resolution(f) is False


def test_existential_to_universal_consequent_not_valid():
    # (∃y P(y) → P(x)) is NOT valid for the same free-variable-under-negation
    # reason; resolution must match Z3.
    f = parse("∃y P(y) → P(x)")
    assert is_valid(f) is False
    assert is_valid_resolution(f) is False


def test_quantifier_swap_non_entailment():
    # The classic non-entailment ∀y∃x L(x,y) ⊭ ∃x∀y L(x,y) (the "someone loves
    # everyone" does not follow from "everyone is loved by someone"). A Skolem
    # collision or mis-scoped quantifier would wrongly make this provable.
    premises = [parse("∀y ∃x Loves(x,y)")]
    assert prove(premises, parse("∃x ∀y Loves(x,y)")) is False


def test_quantifier_swap_entailment_direction_holds():
    # The valid direction ∃x∀y L(x,y) ⊨ ∀y∃x L(x,y) must be proved.
    premises = [parse("∃x ∀y Loves(x,y)")]
    assert prove(premises, parse("∀y ∃x Loves(x,y)")) is True


# ---------------------------------------------------------------------------
# Large adversarial cross-check against Z3 (the heart of the soundness audit)
# ---------------------------------------------------------------------------

import random as _random  # noqa: E402

_PROP_ATOMS = [Atom(name, []) for name in ("P", "Q", "R", "S")]


def _random_prop(depth, rng):
    """Build a random propositional formula over P, Q, R, S up to ``depth``."""
    if depth <= 0 or rng.random() < 0.35:
        atom = rng.choice(_PROP_ATOMS)
        return Not(atom) if rng.random() < 0.4 else atom
    op = rng.choice([And, Or, Implies, "not"])  # skip Iff: CNF blow-up vs bound
    if op == "not":
        return Not(_random_prop(depth - 1, rng))
    return op(_random_prop(depth - 1, rng), _random_prop(depth - 1, rng))


def test_validity_cross_check_against_z3_batch():
    # is_valid_resolution must AGREE with Z3 is_valid on a large random batch,
    # including the many non-valid formulas. The soundness-critical direction is
    # that resolution NEVER reports True when Z3 reports False.
    rng = _random.Random(20240617)
    valids = 0
    for _ in range(600):
        f = _random_prop(rng.randint(1, 3), rng)
        z = is_valid(f)
        r = is_valid_resolution(f, max_steps=40000)
        valids += int(z)
        # Soundness: resolution must never over-claim validity.
        assert not (r and not z), ("UNSOUND validity", f)
        # At this bound and shape, agreement is expected in both directions.
        assert r == z, ("disagreement", f, z, r)
    assert valids > 0  # sanity: the batch actually contained valid formulas


def test_entailment_cross_check_against_z3_batch():
    # prove(premises, conclusion) must equal Z3's validity of (∧premises →
    # conclusion) across a large random batch, including non-entailments. The
    # soundness-critical direction is that prove NEVER returns True for a
    # non-entailment (Z3 False).
    rng = _random.Random(987654321)
    entailments = 0
    for _ in range(600):
        k = rng.randint(1, 3)
        premises = [_random_prop(rng.randint(1, 2), rng) for _ in range(k)]
        conclusion = _random_prop(rng.randint(1, 2), rng)
        big = big_implication(premises, conclusion)
        z = is_valid(big)
        r = prove(premises, conclusion, max_steps=40000)
        entailments += int(z)
        assert not (r and not z), ("UNSOUND entailment", premises, conclusion)
        assert r == z, ("disagreement", premises, conclusion, z, r)
    assert entailments > 0  # sanity: the batch contained real entailments


def test_first_order_non_entailments_batch():
    # A batch of first-order NON-entailments that must all return False. Each is
    # a place a Skolem collision, a mis-scoped free variable, or a missing
    # standardize-apart could leak an unsound True.
    non_entailments = [
        (["∃x P(x)"], "∀y P(y)"),
        (["∀y ∃x R(x,y)"], "∃x ∀y R(x,y)"),
        (["∃x (P(x) ∧ Q(x))"], "∀x (P(x) → Q(x))"),
        (["∀x (P(x) → Q(x))", "Q(b)"], "P(b)"),     # affirming the consequent, FO
        (["P(b)", "∃x Q(x)"], "Q(b)"),
        (["∀x (P(x) ∨ Q(x))"], "∀x P(x) ∨ ∀x Q(x)"),
    ]
    for prem_strs, concl_str in non_entailments:
        premises = [parse(s) for s in prem_strs]
        conclusion = parse(concl_str)
        assert prove(premises, conclusion) is False, (prem_strs, concl_str)


def test_first_order_entailments_batch():
    # The matching valid first-order entailments must all be proved True, so the
    # non-entailment results above are genuine refutations of provability rather
    # than a prover that simply never succeeds.
    entailments = [
        (["∃x ∀y Loves(x,y)"], "∀y ∃x Loves(x,y)"),
        (["∀x (P(x) → Q(x))", "P(b)"], "Q(b)"),
        (["∀x ∀y (R(x,y) → R(y,x))", "R(a,b)"], "R(b,a)"),
        (["∀x P(x)"], "∃x P(x)"),
        (["∀x (P(x) → Q(x))", "∀x (Q(x) → S(x))", "P(c)"], "S(c)"),
    ]
    for prem_strs, concl_str in entailments:
        premises = [parse(s) for s in prem_strs]
        conclusion = parse(concl_str)
        assert prove(premises, conclusion) is True, (prem_strs, concl_str)
