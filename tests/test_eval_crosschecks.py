"""Cross-checks for the eval subsystem: canonicalize / exact_match and validate.

The headline guard is **soundness of canonical exact match against an independent
oracle**: `canonicalize` claims to stay logically equivalent to its input
(invariant P1) and `exact_match` to merge only equivalent formulas. We verify that
against the Z3-backed `formulas_are_equivalent` over random formulas — a wholly
independent decision procedure:

* `canonicalize(f)` is Z3-equivalent to `f` (P1, randomized);
* a formula rewritten by the very transformations canonicalize quotients out
  (commutativity, associativity, operand duplication, double negation) both
  `exact_match`es the original AND is Z3-equivalent to it;
* `exact_match` never fires on a Z3-INequivalent pair (no false merge).

For `validate`, random well-formed formulas validate clean, and each injected
defect (free variable, arity clash, leftover lambda, unparseable text) is flagged
in the right report field.
"""

import random

from unicode_fol_kit import formulas_are_equivalent, MSFLParser, free_variables
from unicode_fol_kit.eval import (
    canonicalize, exact_match, validate, is_wellformed, validate_text,
)
from unicode_fol_kit.fol.nodes import (
    Atom, Variable, Constant,
    Not, And, Or, Xor, Iff, Implies, Quantifier,
)

# Fixed-arity signature so generated formulas are arity-consistent by construction.
_PREDS = [("P", 1), ("Q", 1), ("R", 2)]
_VARS = ["x", "y"]
_CONSTS = ["alice", "bob"]
_BINARY = [And, Or, Xor, Iff, Implies]
_COMMUTATIVE = (And, Or, Xor, Iff)


def _rand_term(rng):
    return Variable(rng.choice(_VARS)) if rng.random() < 0.6 else Constant(rng.choice(_CONSTS))


def _rand_atom(rng):
    name, arity = rng.choice(_PREDS)
    return Atom(name, [_rand_term(rng) for _ in range(arity)])


def _gen(rng, depth):
    """A random classical formula over the fixed signature (may have free vars)."""
    if depth <= 0 or rng.random() < 0.3:
        return _rand_atom(rng)
    kind = rng.choice(["not", "bin", "quant"])
    if kind == "not":
        return Not(_gen(rng, depth - 1))
    if kind == "bin":
        return rng.choice(_BINARY)(_gen(rng, depth - 1), _gen(rng, depth - 1))
    return Quantifier(rng.choice(["∀", "∃"]), Variable(rng.choice(_VARS)),
                      _gen(rng, depth - 1))


def _close(rng, formula):
    """Universally bind every free variable so the result is a sentence."""
    for var in sorted(free_variables(formula), key=lambda v: v.name):
        formula = Quantifier("∀", var, formula)
    return formula


def _closed(rng, depth=3):
    return _close(rng, _gen(rng, depth))


def _rewrite(node, rng):
    """Rewrite by transformations canonicalize must absorb: commute, associate
    (via nested commutes), idempotent operand duplication, and double negation.
    Equivalence- and closedness-preserving (no variable is renamed or freed)."""
    if isinstance(node, Atom):
        out = node
    elif isinstance(node, Not):
        out = Not(_rewrite(node.formula, rng))
    elif isinstance(node, (And, Or, Xor, Iff, Implies)):
        left = _rewrite(node.left, rng)
        right = _rewrite(node.right, rng)
        if isinstance(node, _COMMUTATIVE) and rng.random() < 0.5:
            left, right = right, left
        out = type(node)(left, right)
        if isinstance(node, (And, Or)) and rng.random() < 0.3:
            out = type(node)(out, left)        # P ⋆ P ≡ P: a duplicate to absorb
    elif isinstance(node, Quantifier):
        out = Quantifier(node.type, node.variable, _rewrite(node.formula, rng))
    else:
        out = node
    if rng.random() < 0.3:
        out = Not(Not(out))                    # double negation to collapse
    return out


# ---------------------------------------------------------------------------
# canonicalize / exact_match vs the Z3 oracle
# ---------------------------------------------------------------------------

def test_canonicalize_is_equivalence_preserving():
    """P1: canonicalize(f) is logically equivalent to f (checked by Z3)."""
    rng = random.Random(11)
    for _ in range(50):
        f = _closed(rng)
        assert formulas_are_equivalent(f, canonicalize(f)), f.to_unicode_str()


def test_canonicalize_idempotent():
    """P2: canonicalize is a fixpoint after one application."""
    rng = random.Random(12)
    for _ in range(300):
        f = _closed(rng)
        once = canonicalize(f)
        assert canonicalize(once) == once


def test_exact_match_absorbs_meaning_preserving_rewrites():
    """A commute/associate/dup/double-negation rewrite both exact_matches the
    original and is Z3-equivalent to it."""
    rng = random.Random(13)
    for _ in range(60):
        f = _closed(rng)
        g = _rewrite(f, rng)
        assert exact_match(f, g), f"{f.to_unicode_str()}  !=~  {g.to_unicode_str()}"
        assert formulas_are_equivalent(f, g)


def test_exact_match_never_merges_inequivalent_formulas():
    """exact_match(f, g) ⟹ f and g are Z3-equivalent (no false merge)."""
    rng = random.Random(14)
    for _ in range(200):
        f = _closed(rng)
        g = _closed(rng)
        # If the canonical forms collapse them together, they MUST be equivalent.
        assert (not exact_match(f, g)) or formulas_are_equivalent(f, g)


def test_alpha_variants_match():
    """Bound-variable renaming does not defeat canonical exact match."""
    p = MSFLParser()
    pairs = [
        ("∀x P(x)", "∀y P(y)"),
        ("∀x ∃y R(x, y)", "∀w ∃z R(w, z)"),
        ("∀x (P(x) → ∃y R(x, y))", "∀a (P(a) → ∃b R(a, b))"),
    ]
    for left, right in pairs:
        assert exact_match(p.parse(left), p.parse(right))
        # And a genuine difference is NOT matched away.
    assert not exact_match(p.parse("∀x ∃y R(x, y)"), p.parse("∃y ∀x R(x, y)"))


# ---------------------------------------------------------------------------
# validate / is_wellformed
# ---------------------------------------------------------------------------

def test_random_closed_formulas_are_wellformed():
    """Closed, fixed-arity, lambda-free formulas validate clean."""
    rng = random.Random(15)
    for _ in range(200):
        f = _closed(rng)
        report = validate(f)
        assert report.is_closed
        assert report.arity_consistent
        assert not report.has_lambdas
        assert is_wellformed(f)


def test_validate_flags_free_variable():
    """A free logical variable makes the formula non-closed and is named."""
    f = Atom("P", [Variable("x")])
    report = validate(f)
    assert not report.is_closed
    assert report.free_variable_names == ("x",)
    assert not is_wellformed(f)


def test_validate_flags_arity_conflict():
    """The same predicate at two arities is reported under its namespaced key."""
    f = And(Atom("P", [Constant("alice")]),
            Atom("P", [Constant("alice"), Constant("bob")]))
    report = validate(f)
    assert not report.arity_consistent
    assert report.arity_conflicts[("pred", "P")] == (1, 2)
    assert not is_wellformed(f)


def test_validate_flags_leftover_lambda():
    """Residual lambda machinery is flagged and fails well-formedness."""
    f = MSFLParser().parse("(λx. P(x))(alice)")
    report = validate(f)
    assert report.has_lambdas
    assert not is_wellformed(f)


def test_validate_text_reports_parse_failure():
    """validate_text captures a syntax error instead of raising."""
    report = validate_text("P ∧")
    assert report.parseable is False
    assert report.error
