"""Tests for canonical form and canonical exact match.

Heavy on the property invariants P1–P5 stated in
unicode_fol_kit/eval/canonical.py, plus discrimination tests showing the
canonical form is a normal form for exactly {alpha, commutativity,
associativity, operand-dedup, double-negation} — strictly between raw
structural equality and full logical equivalence.
"""

import random

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Atom,
    And, Or, Xor, Iff, Implies, Not, Quantifier,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction, LukNegation,
    Lambda, LambdaVar,
)
from unicode_fol_kit.atp import formulas_are_equivalent
from unicode_fol_kit.eval.canonical import canonicalize, exact_match

FOL = MSFLParser()
FUZZY = MSFLParser(fuzzy=True)


def P(name="P", *args):
    """Build a (possibly nullary) atom for terse test construction."""
    return Atom(name, list(args))


# ---------------------------------------------------------------------------
# P1 — equivalence-preserving
# ---------------------------------------------------------------------------

class TestP1EquivalencePreserving:
    @pytest.mark.parametrize("formula", [
        "(P ∧ Q) ∨ R",
        "P → (Q ∧ R)",
        "¬(P ∨ Q)",
        "P ↔ (Q ↔ R)",
        "¬¬P",
        "P ∧ P",
        "(P ∧ Q) ∧ R",
        "P ⊕ (Q ⊕ R)",
        "∀x (P(x) → Q(x))",
        "∀x ∃y R(x, y)",
        "¬∀x ¬P(x)",
        "(P → Q) ∧ (R ∨ ¬P)",
    ])
    def test_canonicalize_is_equivalent(self, formula):
        f = FOL.parse(formula)
        assert formulas_are_equivalent(f, canonicalize(f))


# ---------------------------------------------------------------------------
# P2 — idempotency
# ---------------------------------------------------------------------------

class TestP2Idempotent:
    @pytest.mark.parametrize("formula", [
        "P",
        "P ∧ Q",
        "(P ∧ Q) ∨ R",
        "P → (Q ∧ R)",
        "¬¬P",
        "¬¬¬P",
        "P ∧ P",
        "(P ∨ Q) ∨ (R ∨ P)",
        "P ↔ (Q ↔ R)",
        "P ⊕ (Q ⊕ R)",
        "∀x P(x)",
        "∀x ∃y R(x, y)",
        "∀x (P(x) ∧ Q(x))",
        "∀x ∀y (R(x, y) ∧ R(y, x))",
        "∃x (P(x) ∨ P(x))",
        "(∀x P(x)) ∧ (∀y Q(y))",
    ])
    def test_idempotent(self, formula):
        f = FOL.parse(formula)
        once = canonicalize(f)
        twice = canonicalize(once)
        assert once == twice

    def test_idempotent_fuzzy(self):
        f = FUZZY.parse("(P ⊗ Q) ⊗ R")
        once = canonicalize(f)
        assert once == canonicalize(once)


# ---------------------------------------------------------------------------
# P3 — alpha-invariance
# ---------------------------------------------------------------------------

class TestP3AlphaInvariance:
    def test_forall_single(self):
        a = FOL.parse("∀x P(x)")
        b = FOL.parse("∀y P(y)")
        assert canonicalize(a) == canonicalize(b)

    def test_nested_quantifiers(self):
        a = FOL.parse("∀x ∃y R(x, y)")
        b = FOL.parse("∀a ∃b R(a, b)")
        assert canonicalize(a) == canonicalize(b)

    def test_lambda(self):
        a = resolve(Lambda(LambdaVar("x"), Atom("P", [LambdaVar("x")])))
        b = resolve(Lambda(LambdaVar("z"), Atom("P", [LambdaVar("z")])))
        assert canonicalize(a) == canonicalize(b)

    def test_free_variable_untouched(self):
        # x is free here; alpha-normalization must not rename it.
        f = Atom("P", [Variable("x")])
        assert canonicalize(f) == f

    def test_shadowing(self):
        a = FOL.parse("∀x (P(x) ∧ ∃x Q(x))")
        b = FOL.parse("∀a (P(a) ∧ ∃b Q(b))")
        assert canonicalize(a) == canonicalize(b)

    def test_alpha_variant_inside_commutative_group(self):
        # Bound-var renaming under a commutative operand must not perturb the
        # sort order (the alpha-vs-sort interplay).
        a = FOL.parse("(∀x P(x)) ∧ (∃y Q(y))")
        b = FOL.parse("(∀m P(m)) ∧ (∃n Q(n))")
        assert canonicalize(a) == canonicalize(b)


def resolve(node):
    """No-op passthrough: directly-built lambda nodes need no scope resolution."""
    return node


# ---------------------------------------------------------------------------
# P4 — commutativity / associativity invariance
# ---------------------------------------------------------------------------

class TestP4CommAssocInvariance:
    @pytest.mark.parametrize("op", ["∧", "∨", "↔", "⊕"])
    def test_commutativity(self, op):
        a = FOL.parse(f"P {op} Q")
        b = FOL.parse(f"Q {op} P")
        assert canonicalize(a) == canonicalize(b)

    @pytest.mark.parametrize("op", ["∧", "∨", "↔", "⊕"])
    def test_associativity(self, op):
        a = FOL.parse(f"(P {op} Q) {op} R")
        b = FOL.parse(f"P {op} (Q {op} R)")
        assert canonicalize(a) == canonicalize(b)

    def test_mixed_bigger_formula_shuffled(self):
        a = FOL.parse("(P ∧ Q) ∧ (R ∧ S)")
        b = FOL.parse("S ∧ (Q ∧ (P ∧ R))")
        assert canonicalize(a) == canonicalize(b)

    def test_or_shuffle(self):
        a = FOL.parse("(A ∨ B) ∨ (C ∨ D)")
        b = FOL.parse("D ∨ (C ∨ (B ∨ A))")
        assert canonicalize(a) == canonicalize(b)

    def test_fuzzy_strong_conjunction_assoc_comm(self):
        a = FUZZY.parse("(P ⊗ Q) ⊗ R")
        b = FUZZY.parse("R ⊗ (Q ⊗ P)")
        assert canonicalize(a) == canonicalize(b)


# ---------------------------------------------------------------------------
# P5 — double negation
# ---------------------------------------------------------------------------

class TestP5DoubleNegation:
    def test_classical(self):
        a = FOL.parse("¬¬P")
        b = FOL.parse("P")
        assert canonicalize(a) == canonicalize(b)

    def test_nested(self):
        a = FOL.parse("¬¬¬¬P")
        b = FOL.parse("P")
        assert canonicalize(a) == canonicalize(b)

    def test_triple_is_single(self):
        a = FOL.parse("¬¬¬P")
        b = FOL.parse("¬P")
        assert canonicalize(a) == canonicalize(b)

    def test_double_negation_under_connective(self):
        a = FOL.parse("¬¬P ∧ Q")
        b = FOL.parse("P ∧ Q")
        assert canonicalize(a) == canonicalize(b)

    def test_luk_negation_involutive(self):
        a = FUZZY.parse("¬¬P")
        # Łukasiewicz negation is involutive: 1-(1-x)=x.
        assert canonicalize(a) == canonicalize(FUZZY.parse("P"))


# ---------------------------------------------------------------------------
# Operand de-duplication
# ---------------------------------------------------------------------------

class TestOperandDedup:
    def test_and_dedup(self):
        a = FOL.parse("P ∧ P")
        b = FOL.parse("P")
        assert canonicalize(a) == canonicalize(b)

    def test_or_dedup(self):
        a = FOL.parse("P ∨ P")
        b = FOL.parse("P")
        assert canonicalize(a) == canonicalize(b)

    def test_dedup_in_chain(self):
        a = FOL.parse("(P ∧ Q) ∧ P")
        b = FOL.parse("P ∧ Q")
        assert canonicalize(a) == canonicalize(b)

    def test_dedup_preserves_distinct(self):
        # P ∧ Q must NOT collapse to a single operand.
        c = canonicalize(FOL.parse("P ∧ Q"))
        assert c != canonicalize(FOL.parse("P"))
        assert c != canonicalize(FOL.parse("Q"))


# ---------------------------------------------------------------------------
# Discrimination — canonicalize is NOT a full equivalence decision
# ---------------------------------------------------------------------------

class TestDiscrimination:
    def test_and_vs_or(self):
        assert canonicalize(FOL.parse("P ∧ Q")) != canonicalize(FOL.parse("P ∨ Q"))

    def test_forall_vs_exists(self):
        assert canonicalize(FOL.parse("∀x P(x)")) != canonicalize(FOL.parse("∃x P(x)"))

    def test_implication_not_commutative(self):
        a = canonicalize(FOL.parse("P → Q"))
        b = canonicalize(FOL.parse("Q → P"))
        assert a != b

    def test_implication_operand_order_preserved(self):
        # Implies stays Implies(P, Q) with order intact.
        c = canonicalize(Implies(P("P"), P("Q")))
        assert isinstance(c, Implies)
        assert c.left == P("P")
        assert c.right == P("Q")

    def test_not_full_equivalence(self):
        # P → Q and ¬P ∨ Q are logically equivalent but NOT canonically equal:
        # canonicalize does no implication elimination.
        imp = FOL.parse("P → Q")
        disj = FOL.parse("¬P ∨ Q")
        assert formulas_are_equivalent(imp, disj)
        assert canonicalize(imp) != canonicalize(disj)


# ---------------------------------------------------------------------------
# exact_match
# ---------------------------------------------------------------------------

class TestExactMatch:
    def test_canonical_true_for_alpha_comm_variant(self):
        pred = FOL.parse("(∃y Q(y)) ∧ (∀x P(x))")
        ref = FOL.parse("(∀a P(a)) ∧ (∃b Q(b))")
        assert exact_match(pred, ref, canonical=True) is True

    def test_raw_false_for_same_variant(self):
        pred = FOL.parse("(∃y Q(y)) ∧ (∀x P(x))")
        ref = FOL.parse("(∀a P(a)) ∧ (∃b Q(b))")
        assert exact_match(pred, ref, canonical=False) is False

    def test_identical_pair_both_modes(self):
        pred = FOL.parse("∀x (P(x) → Q(x))")
        ref = FOL.parse("∀x (P(x) → Q(x))")
        assert exact_match(pred, ref, canonical=True) is True
        assert exact_match(pred, ref, canonical=False) is True

    def test_default_is_canonical(self):
        pred = FOL.parse("P ∧ Q")
        ref = FOL.parse("Q ∧ P")
        assert exact_match(pred, ref) is True

    def test_canonical_distinguishes_genuinely_different(self):
        pred = FOL.parse("P ∧ Q")
        ref = FOL.parse("P ∨ Q")
        assert exact_match(pred, ref, canonical=True) is False


# ---------------------------------------------------------------------------
# Constants vs variables — Constant('a') is a genuine constant, not renamed
# ---------------------------------------------------------------------------

class TestConstantsNotRenamed:
    def test_constant_untouched(self):
        a = Quantifier("∀", Variable("x"), Atom("P", [Variable("x"), Constant("a")]))
        c = canonicalize(a)
        # the bound x is renamed to q0; the constant a is preserved verbatim.
        assert c == Quantifier("∀", Variable("q0"),
                               Atom("P", [Variable("q0"), Constant("a")]))


# ---------------------------------------------------------------------------
# Regression: non-idempotent connectives must NOT be de-duplicated (P1).
# `a ⊕ a ≡ ⊥`, `a ↔ a ≡ ⊤`, and the Łukasiewicz t-norm/t-conorm are not
# idempotent, so removing a repeated operand would change the truth value.
# ---------------------------------------------------------------------------

class TestNonIdempotentNoDedup:
    def test_xor_self_not_collapsed(self):
        f = FOL.parse("P ⊕ P")
        c = canonicalize(f)
        # Must NOT become P; P ⊕ P is contradictory, P is not.
        assert formulas_are_equivalent(f, c)
        assert c != canonicalize(FOL.parse("P"))

    def test_iff_self_not_collapsed(self):
        f = FOL.parse("P ↔ P")
        c = canonicalize(f)
        # P ↔ P is a tautology, P is not.
        assert formulas_are_equivalent(f, c)
        assert c != canonicalize(FOL.parse("P"))

    def test_xor_triple_keeps_meaning(self):
        # P ⊕ Q ⊕ Q ≡ P, but the canonical form must stay equivalent (it is not
        # required to simplify Q ⊕ Q away — only to not corrupt the value).
        f = FOL.parse("(P ⊕ Q) ⊕ Q")
        assert formulas_are_equivalent(f, canonicalize(f))

    def test_fuzzy_strong_conjunction_self_not_collapsed(self):
        f = FUZZY.parse("P ⊗ P")
        c = canonicalize(f)
        # x ⊗ x = max(0, 2x-1) ≢ x, so P ⊗ P must not collapse to P.
        assert c != canonicalize(FUZZY.parse("P"))

    def test_idempotent_connectives_still_dedup(self):
        # The legitimate dedup (∧ ∨ and fuzzy min/max) must keep working.
        assert canonicalize(FOL.parse("P ∧ P")) == canonicalize(FOL.parse("P"))
        assert canonicalize(FOL.parse("P ∨ P")) == canonicalize(FOL.parse("P"))
        assert (canonicalize(FUZZY.parse("P ∧ P"))
                == canonicalize(FUZZY.parse("P")))  # WeakConjunction (min)
        assert (canonicalize(FUZZY.parse("P ∨ P"))
                == canonicalize(FUZZY.parse("P")))  # WeakDisjunction (max)


# ---------------------------------------------------------------------------
# Regression: double-negation collapse that EXPOSES a nested same-class
# commutative node must re-flatten into the parent group (P2 / P4 / dedup).
# Before the fix, `¬¬(P ∨ Q) ∨ Q` canonicalized to `P ∨ Q ∨ Q` (a surviving
# duplicate that only a SECOND pass removed — i.e. non-idempotent).
# ---------------------------------------------------------------------------

class TestDoubleNegExposesNestedGroup:
    @pytest.mark.parametrize("formula,expected", [
        ("¬¬(P ∨ Q) ∨ Q", "P ∨ Q"),
        ("¬¬(P ∧ Q) ∧ Q", "P ∧ Q"),
        ("P ∧ Q ∧ ¬¬(Q ∧ R)", "P ∧ Q ∧ R"),
        ("(A ∨ B) ∨ ¬¬(B ∨ C)", "A ∨ B ∨ C"),
    ])
    def test_reflatten_after_double_neg(self, formula, expected):
        f = FOL.parse(formula)
        c = canonicalize(f)
        assert c == canonicalize(c)                 # idempotent in ONE pass
        assert c == canonicalize(FOL.parse(expected))
        assert formulas_are_equivalent(f, c)

    def test_xor_reflatten_stays_equivalent(self):
        # Re-flatten must not silently dedup the non-idempotent ⊕.
        f = FOL.parse("¬¬(P ⊕ Q) ⊕ Q")
        c = canonicalize(f)
        assert c == canonicalize(c)
        assert formulas_are_equivalent(f, c)


# ---------------------------------------------------------------------------
# Regression: alpha-vs-sort ordering trap. A commutative group sitting INSIDE
# quantifiers whose operands reference different ENCLOSING binders must order
# deterministically and idempotently. Before the fix, the sort key depended on
# the (changing) enclosing bound-variable names, so `¬∀y ¬∀x (P(x) ∧ P(y))`
# and its ∧-commuted twin canonicalized differently, and some formulas were
# not idempotent in a single pass.
# ---------------------------------------------------------------------------

class TestAlphaVsSortInterplay:
    def _P(self, name, var):
        return Atom(name, [Variable(var)])

    def test_nested_quantifier_comm_invariance(self):
        f1 = Not(Quantifier("∀", Variable("y"),
                 Not(Quantifier("∀", Variable("x"),
                     And(self._P("P", "x"), self._P("P", "y"))))))
        f2 = Not(Quantifier("∀", Variable("y"),
                 Not(Quantifier("∀", Variable("x"),
                     And(self._P("P", "y"), self._P("P", "x"))))))
        assert canonicalize(f1) == canonicalize(f2)

    def test_commutative_group_under_quantifiers_idempotent(self):
        f = Quantifier("∀", Variable("x"), Quantifier("∃", Variable("w"),
                Xor(Implies(Quantifier("∃", Variable("z"), self._P("P", "x")),
                            self._P("Q", "w")),
                    Or(self._P("R", "x"), self._P("R", "w")))))
        c = canonicalize(f)
        assert c == canonicalize(c)
        assert formulas_are_equivalent(f, c)

    def test_distinct_enclosing_operands_not_overcollapsed(self):
        # R(x) ∨ R(w) references two distinct enclosing binders: must keep both.
        f = Quantifier("∀", Variable("x"), Quantifier("∃", Variable("w"),
                Or(self._P("R", "x"), self._P("R", "w"))))
        c = canonicalize(f)
        assert formulas_are_equivalent(f, c)
        assert c.count(Atom) == 2

    def test_alpha_equivalent_operands_dedup_under_quantifier(self):
        # (∀x P(x)) ∧ (∀y P(y)) — alpha-equivalent conjuncts collapse to one.
        f = FOL.parse("(∀x P(x)) ∧ (∀y P(y))")
        assert canonicalize(f) == canonicalize(FOL.parse("∀x P(x)"))


# ---------------------------------------------------------------------------
# Randomized property tests — independently stress P1–P4 across many cases.
# ---------------------------------------------------------------------------

_RNG_VARS = ["x", "y", "z", "w", "u", "v"]


def _rand_quantified(depth, scope, rng):
    """Build a random closed-ish quantified formula over unary predicates."""
    if depth <= 0 or (rng.random() < 0.4 and scope):
        return Atom(rng.choice(["P", "Q", "R"]),
                    [Variable(rng.choice(scope))]) if scope else Atom("P", [])
    r = rng.random()
    if r < 0.5 and scope:
        cls = rng.choice([And, Or, Xor, Iff, Implies])
        return cls(_rand_quantified(depth - 1, scope, rng),
                   _rand_quantified(depth - 1, scope, rng))
    if r < 0.72:
        return Not(_rand_quantified(depth - 1, scope, rng))
    var = rng.choice(_RNG_VARS)
    return Quantifier(rng.choice(["∀", "∃"]), Variable(var),
                      _rand_quantified(depth - 1, scope + [var], rng))


def _rand_propositional(depth, rng):
    """Build a random closed propositional formula over nullary atoms."""
    if depth <= 0 or rng.random() < 0.35:
        return Atom(rng.choice(["P", "Q", "R", "S"]), [])
    r = rng.random()
    if r < 0.65:
        cls = rng.choice([And, Or, Xor, Iff, Implies])
        return cls(_rand_propositional(depth - 1, rng),
                   _rand_propositional(depth - 1, rng))
    return Not(_rand_propositional(depth - 1, rng))


def _alpha_rename(node, env, fresh):
    """Capture-safe alpha-renaming: every quantifier gets a globally-fresh name."""
    if isinstance(node, Variable):
        return Variable(env.get(node.name, node.name))
    if isinstance(node, Quantifier):
        new = f"r{fresh[0]}"
        fresh[0] += 1
        inner = dict(env)
        inner[node.variable.name] = new
        return Quantifier(node.type, Variable(new),
                          _alpha_rename(node.formula, inner, fresh))
    if not node._child_nodes():
        return node
    return node.map_children(lambda c: _alpha_rename(c, dict(env), fresh))


_COMM_CLASSES = (And, Or, Xor, Iff,
                 WeakConjunction, WeakDisjunction,
                 StrongConjunction, StrongDisjunction)


def _shuffle_comm(node, rng):
    """Randomly reassociate and commute every commutative group (meaning-preserving)."""
    if isinstance(node, _COMM_CLASSES):
        cls = type(node)
        ops = []
        stack = [node]
        # flatten same-class chain
        flat = []

        def flatten(n):
            for side in (n.left, n.right):
                if isinstance(side, cls):
                    flatten(side)
                else:
                    flat.append(side)
        flatten(node)
        ops = [_shuffle_comm(o, rng) for o in flat]
        rng.shuffle(ops)
        res = ops[0]
        for o in ops[1:]:
            res = cls(res, o)
        return res
    if not node._child_nodes():
        return node
    return node.map_children(lambda c: _shuffle_comm(c, rng))


class TestRandomizedProperties:
    def test_idempotent_alpha_comm_quantified(self):
        rng = random.Random(20240623)
        for _ in range(400):
            f = _rand_quantified(5, [], rng)
            c = canonicalize(f)
            # P2 idempotency in a single re-application.
            assert canonicalize(c) == c
            # P3 alpha-invariance.
            assert canonicalize(_alpha_rename(f, {}, [0])) == c
            # P4 comm/assoc-invariance.
            assert canonicalize(_shuffle_comm(f, rng)) == c

    def test_roundtrip_quantified(self):
        rng = random.Random(7)
        for _ in range(200):
            f = _rand_quantified(5, [], rng)
            c = canonicalize(f)
            # Canonical output round-trips through the parser unchanged.
            assert FOL.parse(c.to_unicode_str()) == c

    def test_equivalence_preserving_propositional(self):
        rng = random.Random(99)
        for _ in range(150):
            f = _rand_propositional(5, rng)
            c = canonicalize(f)
            assert canonicalize(c) == c                      # P2
            assert formulas_are_equivalent(f, c)             # P1 (Z3)
