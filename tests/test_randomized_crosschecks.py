"""Randomized cross-checks for the 0.5.0 semantics subsystems (seeded).

These complement the example-based suites with property tests that pit two
independent computations against each other over many random inputs:

* **Many-valued compiled path == reference** — the new compiled enumeration fast
  path (``manyvalued._compile`` / ``_prepare_enumeration``) must agree with the
  reference walker ``kleene_value`` on EVERY assignment, for random formulas. This
  is the correctness guard for the enumeration speed-up.
* **Strong-Kleene algebra** — De Morgan, double negation, the material-implication
  and Xor/Iff definitions hold as ``kleene_value`` identities over all valuations;
  plus the K3-vs-LP headline facts (excluded middle, paraconsistency).
* **Second-order classical core == Tarski** — on a formula with no second-order
  quantifier, ``satisfies_so`` agrees with the independent first-order
  ``tarski.satisfies``.
* **Second-order quantifier duality** — ``∀P φ ≡ ¬∃P ¬φ`` and ``∃P φ ≡ ¬∀P ¬φ``
  over random finite structures: a theorem the evaluator must satisfy regardless
  of how it enumerates relations.

All randomness is seeded, so failures reproduce exactly.
"""

import itertools
import random

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Variable, Constant, Number, Function,
    Not, And, Or, Xor, Implies, Iff, Quantifier,
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction, LukImplication, LukEquivalence,
    Box, Diamond, Always, Eventually, Next, Until,
    Knows, Believes, Obligatory, Permitted,
    SecondOrderQuantifier,
)
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.semantics.manyvalued import (
    kleene_value, is_valid, entails, TRUTH_VALUES, _prepare_enumeration,
)
from unicode_fol_kit.semantics.tarski import Structure, satisfies
from unicode_fol_kit.semantics.secondorder import satisfies_so, holds


# ---------------------------------------------------------------------------
# Generators (all driven by a seeded rng)
# ---------------------------------------------------------------------------

_PROP_ATOMS = ["P", "Q", "R"]
_BINARY = {"and": And, "or": Or, "xor": Xor, "implies": Implies, "iff": Iff}


def _rand_prop(rng, depth):
    """A random propositional classical formula over P/Q/R (arity-0 atoms)."""
    if depth <= 0 or rng.random() < 0.3:
        return Atom(rng.choice(_PROP_ATOMS), [])
    kind = rng.choice(["not", "and", "or", "xor", "implies", "iff"])
    if kind == "not":
        return Not(_rand_prop(rng, depth - 1))
    return _BINARY[kind](_rand_prop(rng, depth - 1), _rand_prop(rng, depth - 1))


def _all_valuations(keys):
    """Every map of ``keys`` to {0.0, 0.5, 1.0}."""
    for combo in itertools.product(TRUTH_VALUES, repeat=len(keys)):
        yield dict(zip(keys, combo))


def _atom_keys(*formulas):
    """Distinct propositional atom keys across the formulas, first-seen order."""
    keys, seen = [], set()
    for f in formulas:
        for atom in f.atoms():
            k = atom.to_unicode_str()
            if k not in seen:
                seen.add(k)
                keys.append(k)
    return keys


# ---------------------------------------------------------------------------
# Many-valued: compiled fast path == reference kleene_value
# ---------------------------------------------------------------------------

def test_manyvalued_compiled_matches_reference():
    """``_prepare_enumeration``'s compiled evaluator == ``kleene_value`` everywhere.

    For each random formula, compare the compiled value against the reference
    walker on every one of the 3**n assignments. This is exactly the path
    is_valid/is_satisfiable/entails now take, so equality here certifies the
    speed-up changes nothing semantically.
    """
    rng = random.Random(0xC0FFEE)
    for _ in range(300):
        formula = _rand_prop(rng, 4)
        keys, (evaluate,) = _prepare_enumeration([formula], None)
        for combo in itertools.product(TRUTH_VALUES, repeat=len(keys)):
            valuation = dict(zip(keys, combo))
            assert evaluate(combo) == kleene_value(formula, valuation), (
                f"compiled != reference for {formula.to_unicode_str()} "
                f"at {valuation}"
            )


# ---------------------------------------------------------------------------
# Many-valued: strong-Kleene algebraic identities (hold for every valuation)
# ---------------------------------------------------------------------------

def _kleene_equiv(a, b, keys):
    """True iff a and b have equal kleene_value under every valuation of keys."""
    return all(
        kleene_value(a, v) == kleene_value(b, v) for v in _all_valuations(keys)
    )


def test_manyvalued_strong_kleene_identities():
    """De Morgan, double negation, →/⊕/↔ definitions are kleene_value identities."""
    rng = random.Random(20260624)
    for _ in range(120):
        a = _rand_prop(rng, 3)
        b = _rand_prop(rng, 3)
        keys = _atom_keys(a, b)
        # Double negation.
        assert _kleene_equiv(Not(Not(a)), a, keys)
        # De Morgan (both directions).
        assert _kleene_equiv(Not(And(a, b)), Or(Not(a), Not(b)), keys)
        assert _kleene_equiv(Not(Or(a, b)), And(Not(a), Not(b)), keys)
        # Material implication a → b ≡ ¬a ∨ b.
        assert _kleene_equiv(Implies(a, b), Or(Not(a), b), keys)
        # Biconditional a ↔ b ≡ (a → b) ∧ (b → a).
        assert _kleene_equiv(Iff(a, b), And(Implies(a, b), Implies(b, a)), keys)
        # Exclusive or a ⊕ b ≡ (a ∨ b) ∧ ¬(a ∧ b).
        assert _kleene_equiv(Xor(a, b), And(Or(a, b), Not(And(a, b))), keys)


def test_k3_vs_lp_headline_facts():
    """The two logics differ exactly where the textbooks say they do."""
    P = Atom("P", [])
    Q = Atom("Q", [])
    lem = Or(P, Not(P))                  # excluded middle
    ncon = Not(And(P, Not(P)))           # non-contradiction
    # Excluded middle: LP-valid, K3-invalid (P = ½ gives ½, undesignated in K3).
    assert is_valid(lem, "LP") is True
    assert is_valid(lem, "K3") is False
    # Non-contradiction: LP-valid, K3-invalid (same ½ witness).
    assert is_valid(ncon, "LP") is True
    assert is_valid(ncon, "K3") is False
    # Explosion P, ¬P ⊨ Q : holds vacuously in K3, FAILS in LP (paraconsistency).
    assert entails([P, Not(P)], Q, "K3") is True
    assert entails([P, Not(P)], Q, "LP") is False


# ---------------------------------------------------------------------------
# Second-order generators + structures
# ---------------------------------------------------------------------------

_OBJ_VARS = ["x", "y"]


def _rand_matrix(rng, depth, preds):
    """A random open formula over object vars x/y and the given (name, arity) preds."""
    if depth <= 0 or rng.random() < 0.4:
        name, arity = rng.choice(preds)
        args = [Variable(rng.choice(_OBJ_VARS)) for _ in range(arity)]
        return Atom(name, args)
    kind = rng.choice(["not", "and", "or", "implies", "iff"])
    if kind == "not":
        return Not(_rand_matrix(rng, depth - 1, preds))
    return _BINARY[kind](_rand_matrix(rng, depth - 1, preds),
                         _rand_matrix(rng, depth - 1, preds))


def _close(rng, matrix):
    """Bind x and y with random ∀/∃ so the formula is object-closed."""
    formula = matrix
    for var in ("y", "x"):
        formula = Quantifier(rng.choice(["∀", "∃"]), Variable(var), formula)
    return formula


def _rand_structure(rng):
    """A random finite Structure interpreting Q (arity 1) and R (arity 2)."""
    n = rng.randint(1, 3)
    domain = set(range(n))
    q_ext = {(d,) for d in range(n) if rng.random() < 0.5}
    r_ext = {(a, b) for a in range(n) for b in range(n) if rng.random() < 0.4}
    return Structure(domain=domain, predicates={("Q", 1): q_ext, ("R", 2): r_ext})


def test_secondorder_classical_core_matches_tarski():
    """With no ∀P/∃P, satisfies_so agrees with the independent Tarski evaluator."""
    rng = random.Random(777)
    preds = [("Q", 1), ("R", 2)]
    for _ in range(150):
        formula = _close(rng, _rand_matrix(rng, 3, preds))
        structure = _rand_structure(rng)
        assert satisfies_so(formula, structure, {}, {}) == \
            satisfies(formula, structure, {}), formula.to_unicode_str()


def test_secondorder_quantifier_duality():
    """∀P φ ≡ ¬∃P ¬φ and ∃P φ ≡ ¬∀P ¬φ over random finite structures.

    P is monadic here (arity 1); the body mixes the bound P with the structure's
    Q/R. The duality is a theorem of the semantics, independent of how relations
    are enumerated, so agreement cross-checks the enumerator against itself in a
    non-trivial way.
    """
    rng = random.Random(31337)
    preds = [("P", 1), ("Q", 1), ("R", 2)]
    for _ in range(120):
        inner = _close(rng, _rand_matrix(rng, 3, preds))
        structure = _rand_structure(rng)

        forall_p = SecondOrderQuantifier("∀", "P", 1, inner)
        exists_p = SecondOrderQuantifier("∃", "P", 1, inner)
        dual_of_forall = Not(SecondOrderQuantifier("∃", "P", 1, Not(inner)))
        dual_of_exists = Not(SecondOrderQuantifier("∀", "P", 1, Not(inner)))

        assert holds(forall_p, structure) == holds(dual_of_forall, structure)
        assert holds(exists_p, structure) == holds(dual_of_exists, structure)


# ---------------------------------------------------------------------------
# Parser <-> renderer round-trip: parse(node.to_unicode_str()) == node
# ---------------------------------------------------------------------------
#
# Terminal classes constrain the names so each rendered token re-lexes to the
# same kind: VARIABLE = a single lowercase letter (x/y/z); NAME (≥2 lowercase,
# used for constants and function symbols) = alice/bob, ff/gg; CONSTANT = c_…;
# PREDICATE = uppercase P/Q/R/S; agents (K_a / B_a) are lowercase. Only
# alphabetic predicates are generated (infix =,<,… are covered by the
# equivalence corpus), so every produced formula renders to a parseable string
# whose AST must come back identical — exercising the renderer's precedence
# parenthesisation against the grammar's no-mixing / associativity rules.

_VARS = ["x", "y", "z"]
_CONSTS = ["alice", "bob", "c_1", "c_2"]
_FUNCS = ["ff", "gg"]
_PREDS = ["P", "Q", "R", "S"]
_AGENTS = ["alice", "bob"]


def _rand_term(rng, depth):
    """A random term: variable, constant, number, or (small) function application."""
    if depth <= 0:
        choice = rng.choice(["var", "const", "num"])
    else:
        choice = rng.choice(["var", "const", "num", "func", "func"])
    if choice == "var":
        return Variable(rng.choice(_VARS))
    if choice == "const":
        return Constant(rng.choice(_CONSTS))
    if choice == "num":
        return Number(rng.choice([0, 1, 7, 42]))
    arity = rng.randint(1, 2)
    return Function(rng.choice(_FUNCS),
                    [_rand_term(rng, depth - 1) for _ in range(arity)])


def _rand_atom(rng, term_depth):
    """A random predicate atom P/Q/R/S of arity 0–2 over random terms."""
    arity = rng.randint(0, 2)
    return Atom(rng.choice(_PREDS),
                [_rand_term(rng, term_depth) for _ in range(arity)])


def _gen(rng, depth, binary, unary_prefix, *, modal=False, second_order=False):
    """Generic random formula generator parameterised by the mode's operators.

    ``binary`` is the list of binary node classes (each ``cls(a, b)``);
    ``unary_prefix`` the list of unary prefix classes (each ``cls(child)``).
    ``modal`` adds agent operators + Until; ``second_order`` adds ∀P/∃P over a
    monadic predicate variable.
    """
    if depth <= 0 or rng.random() < 0.25:
        return _rand_atom(rng, term_depth=2)

    forms = ["binary", "unary", "quant"]
    if modal:
        forms += ["agent", "until"]
    if second_order:
        forms += ["so"]
    kind = rng.choice(forms)

    if kind == "binary":
        cls = rng.choice(binary)
        return cls(_gen(rng, depth - 1, binary, unary_prefix,
                        modal=modal, second_order=second_order),
                   _gen(rng, depth - 1, binary, unary_prefix,
                        modal=modal, second_order=second_order))
    if kind == "unary":
        cls = rng.choice(unary_prefix)
        return cls(_gen(rng, depth - 1, binary, unary_prefix,
                        modal=modal, second_order=second_order))
    if kind == "quant":
        return Quantifier(rng.choice(["∀", "∃"]), Variable(rng.choice(_VARS)),
                          _gen(rng, depth - 1, binary, unary_prefix,
                               modal=modal, second_order=second_order))
    if kind == "agent":
        cls = rng.choice([Knows, Believes])
        return cls(rng.choice(_AGENTS),
                   _gen(rng, depth - 1, binary, unary_prefix, modal=modal))
    if kind == "until":
        return Until(_gen(rng, depth - 1, binary, unary_prefix, modal=modal),
                     _gen(rng, depth - 1, binary, unary_prefix, modal=modal))
    # second-order: a monadic ∀Z/∃Z whose body applies Z at arity 1 (so the
    # parser re-infers arity 1 and the round-trip is stable). The bound name "Z"
    # is deliberately NOT in _PREDS, so the random sub-formula never applies it at
    # a clashing arity.
    body = And(Atom("Z", [Variable("x")]),
               _gen(rng, depth - 1, binary, unary_prefix, second_order=second_order))
    return SecondOrderQuantifier(rng.choice(["∀", "∃"]), "Z", 1,
                                 Quantifier("∀", Variable("x"), body))


_CLASSICAL_BINARY = [And, Or, Xor, Implies, Iff]
_CLASSICAL_UNARY = [Not]
_LUK_BINARY = [WeakConjunction, WeakDisjunction, StrongConjunction,
               StrongDisjunction, LukImplication, LukEquivalence]
_LUK_UNARY = [LukNegation]
_MODAL_UNARY = [Not, Box, Diamond, Always, Eventually, Next, Obligatory, Permitted]


def _assert_roundtrips(parser, node):
    """parse(node.to_unicode_str()) must equal node."""
    rendered = node.to_unicode_str()
    reparsed = parser.parse(rendered)
    assert reparsed == node, (
        f"round-trip mismatch:\n  node     = {node!r}\n  rendered = {rendered!r}"
        f"\n  reparsed = {reparsed!r}"
    )


def test_roundtrip_random_fol():
    """Random FOL formulas survive render -> parse unchanged."""
    rng = random.Random(101)
    parser = MSFLParser()
    for _ in range(250):
        _assert_roundtrips(parser, _gen(rng, 4, _CLASSICAL_BINARY, _CLASSICAL_UNARY))


def test_roundtrip_random_modal():
    """Random modal formulas (□ ◇ Ⓖ Ⓕ Ⓝ Ⓞ Ⓟ K_a B_a Ⓤ) survive render -> parse."""
    rng = random.Random(202)
    parser = MSFLParser(modal=True)
    for _ in range(250):
        _assert_roundtrips(
            parser, _gen(rng, 4, _CLASSICAL_BINARY, _MODAL_UNARY, modal=True))


def test_roundtrip_random_fuzzy():
    """Random Łukasiewicz (FL) formulas (∧ ∨ ⊗ ⊕ → ↔ ¬) survive render -> parse."""
    rng = random.Random(303)
    parser = MSFLParser(fuzzy=True)
    for _ in range(250):
        _assert_roundtrips(parser, _gen(rng, 4, _LUK_BINARY, _LUK_UNARY))


def test_roundtrip_random_second_order():
    """Random second-order formulas (∀P/∃P + classical) survive render -> parse."""
    rng = random.Random(404)
    parser = MSFLParser(second_order=True)
    for _ in range(200):
        _assert_roundtrips(
            parser,
            _gen(rng, 4, _CLASSICAL_BINARY, _CLASSICAL_UNARY, second_order=True))
