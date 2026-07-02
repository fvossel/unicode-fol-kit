"""Hand-checked tests for relevant logic B (simplified Routley–Meyer semantics).

Every (in)validity claim below is justified in a comment by direct appeal to the
truth clauses of the Priest–Sylvan simplified semantics:

- ``w ⊨ ¬A``            iff ``w* ⊭ A``                          (Routley star)
- ``w ⊨ A → B``, w ∈ N  iff for ALL ``x ∈ W``: ``x ⊨ A ⇒ x ⊨ B``
- ``w ⊨ A → B``, w ∉ N  iff for all ``R(w, x, y)``: ``x ⊨ A ⇒ y ⊨ B``

with validity = truth at every normal world of every interpretation. The
classical cross-checks use the Z3 oracle ``is_valid`` (soundness: B ⊆ CL —
every B-theorem is classically valid). The property test makes the inclusion
executable: a 1-world simplified RM interpretation IS a classical valuation.
"""

import random

import pytest

from unicode_fol_kit import (
    MSFLParser, is_valid,
    Atom, Not, And, Or, Implies, Iff, Box,
)
from unicode_fol_kit.semantics.relevant import (
    RelevantModel, rel_satisfies, rel_countermodel, rel_valid,
)

p = MSFLParser().parse


# ---------------------------------------------------------------------------
# Theorems of B (valid in every simplified RM interpretation)
# ---------------------------------------------------------------------------
# Each of these is *pointwise*: the consequent holds at any world where the
# antecedent holds, in ANY interpretation, so the normal-world →-clause
# ("every A-world is a B-world") is satisfied at every normal world.

VALID_IN_B = [
    # x ⊨ P ⇒ x ⊨ P, trivially.
    "P → P",
    # x ⊨ P ∧ Q ⇒ x ⊨ P (resp. Q) by the ∧ clause.
    "(P ∧ Q) → P",
    "(P ∧ Q) → Q",
    # x ⊨ P (resp. Q) ⇒ x ⊨ P ∨ Q by the ∨ clause.
    "P → (P ∨ Q)",
    "Q → (P ∨ Q)",
    # ∧/∨ are pointwise truth-functional, so distribution holds at every world.
    "(P ∧ (Q ∨ R)) → ((P ∧ Q) ∨ (P ∧ R))",
    # x ⊨ ¬¬P iff x** ⊨ P iff x ⊨ P, since * is an involution — both directions.
    "¬¬P → P",
    "P → ¬¬P",
    # P ↔ P unfolds to (P → P) ∧ (P → P).
    "P ↔ P",
    # x ⊨ P ↔ Q means x ⊨ (P→Q) ∧ (Q→P), which entails x ⊨ P → Q pointwise
    # (an instance of (A ∧ B) → A with A = P→Q).
    "(P ↔ Q) → (P → Q)",
]


@pytest.mark.parametrize("text", VALID_IN_B)
def test_valid_in_B(text):
    formula = p(text)
    assert rel_valid(formula, max_worlds=2), f"{text} should be B-valid"
    # Sanity cross-check with the Z3 oracle: B ⊆ CL, so every B-theorem
    # must also be classically valid.
    assert is_valid(formula), f"{text} should be classically valid"


# ---------------------------------------------------------------------------
# NON-theorems of B — each has a 2-world countermodel (one normal w0, one
# non-normal w1), spelled out in the comment and re-built by hand below.
# ---------------------------------------------------------------------------

INVALID_IN_B = [
    # Positive paradox. V(P)={w1}, V(Q)={w0}, R(w1,w0,w0), star = identity:
    # w1 ⊨ P but w1 ⊭ Q→P (the triple has w0 ⊨ Q yet w0 ⊭ P), so the
    # normal-world clause for the outer → fails at w0.
    "P → (Q → P)",
    # Explosion / ECQ. star swaps w0↔w1, V(P)={w1}, V(Q)=∅:
    # w1 ⊨ P and w1 ⊨ ¬P (w1* = w0 ⊭ P), yet w1 ⊭ Q.
    "(P ∧ ¬P) → Q",
    # Irrelevant tautological consequent. star swaps, V(P)={w1}, V(Q)={w0}:
    # w1 ⊨ P but w1 ⊭ Q (V) and w1 ⊭ ¬Q (w1* = w0 ⊨ Q).
    "P → (Q ∨ ¬Q)",
    # Peirce. R = ∅ and V(P) = ∅: w1 ⊨ (P→Q)→P VACUOUSLY (no R-triples at
    # w1), while w1 ⊭ P.
    "((P → Q) → P) → P",
    # LEM is not a theorem of B. star swaps, V(P)={w1}: w0 ⊭ P and
    # w0 ⊭ ¬P (w0* = w1 ⊨ P), so the normal w0 refutes the disjunction.
    "P ∨ ¬P",
    # Disjunctive syllogism. star swaps, V(P)={w1}, V(Q)=∅:
    # w1 ⊨ P∨Q and w1 ⊨ ¬P (w1* = w0 ⊭ P), yet w1 ⊭ Q.
    "((P ∨ Q) ∧ ¬P) → Q",
    # Contraction (a bonus non-theorem of B). R = {(w1,w1,w0)}, star = id,
    # V(P)=V(Q)={w1}: w1 ⊨ P→(P→Q) (its sole triple needs w0 ⊨ P→Q, true at
    # the normal w0 since the only P-world w1 has Q) but w1 ⊭ P→Q (the triple
    # has w1 ⊨ P, w0 ⊭ Q).
    "(P → (P → Q)) → (P → Q)",
]


@pytest.mark.parametrize("text", INVALID_IN_B)
def test_invalid_in_B(text):
    formula = p(text)
    result = rel_countermodel(formula, max_worlds=2)
    assert result is not None, f"{text} should have a ≤2-world countermodel"
    model, world = result
    # The failure world is the (single) normal world, and rel_satisfies
    # confirms the refutation.
    assert world in model.normal
    assert not rel_satisfies(model, world, formula)
    assert not rel_valid(formula, max_worlds=2)


# ---------------------------------------------------------------------------
# The hand-built countermodels from the comments above, replayed clause by
# clause with rel_satisfies.
# ---------------------------------------------------------------------------

def test_positive_paradox_hand_model():
    # ⟨W={w0,w1}, N={w0}, * = id, R={(w1,w0,w0)}, V(P)={w1}, V(Q)={w0}⟩.
    m = RelevantModel(
        worlds=("w0", "w1"), normal={"w0"},
        R={("w1", "w0", "w0")},
        valuation={"P": {"w1"}, "Q": {"w0"}},
    )
    assert rel_satisfies(m, "w1", p("P"))            # w1 ∈ V(P)
    assert rel_satisfies(m, "w0", p("Q"))            # w0 ∈ V(Q)
    # w1 ⊭ Q → P: the sole triple R(w1,w0,w0) has w0 ⊨ Q but w0 ⊭ P.
    assert not rel_satisfies(m, "w1", p("Q → P"))
    # So some P-world (namely w1) is not a (Q→P)-world: the paradox fails at w0.
    assert not rel_satisfies(m, "w0", p("P → (Q → P)"))


def test_explosion_hand_model():
    # ⟨W={w0,w1}, N={w0}, * swaps w0↔w1, R=∅, V(P)={w1}, V(Q)=∅⟩.
    m = RelevantModel(
        worlds=("w0", "w1"), normal={"w0"},
        star={"w0": "w1", "w1": "w0"},
        valuation={"P": {"w1"}},
    )
    # w1 ⊨ P (valuation) and w1 ⊨ ¬P (w1* = w0 ⊭ P): an inconsistent world.
    assert rel_satisfies(m, "w1", p("P ∧ ¬P"))
    assert not rel_satisfies(m, "w1", p("Q"))
    # A (P∧¬P)-world that is not a Q-world refutes explosion at the normal w0.
    assert not rel_satisfies(m, "w0", p("(P ∧ ¬P) → Q"))
    # The same model refutes LEM at w0: w0 ⊭ P, and w0 ⊭ ¬P since w0* = w1 ⊨ P.
    assert not rel_satisfies(m, "w0", p("P"))
    assert not rel_satisfies(m, "w0", p("¬P"))
    assert not rel_satisfies(m, "w0", p("P ∨ ¬P"))


def test_peirce_hand_model():
    # ⟨W={w0,w1}, N={w0}, * = id, R=∅, V=∅⟩: with no R-triples at w1, EVERY
    # implication holds vacuously at w1 — in particular (P→Q)→P — yet w1 ⊭ P.
    m = RelevantModel(("w0", "w1"), {"w0"})
    assert rel_satisfies(m, "w1", p("(P → Q) → P"))
    assert not rel_satisfies(m, "w1", p("P"))
    assert not rel_satisfies(m, "w0", p("((P → Q) → P) → P"))


def test_contraction_hand_model():
    # ⟨W={w0,w1}, N={w0}, * = id, R={(w1,w1,w0)}, V(P)=V(Q)={w1}⟩.
    m = RelevantModel(
        worlds=("w0", "w1"), normal={"w0"},
        R={("w1", "w1", "w0")},
        valuation={"P": {"w1"}, "Q": {"w1"}},
    )
    # w0 ⊨ P → Q: the only P-world is w1, and w1 ⊨ Q.
    assert rel_satisfies(m, "w0", p("P → Q"))
    # w1 ⊭ P → Q: the triple R(w1,w1,w0) has w1 ⊨ P but w0 ⊭ Q.
    assert not rel_satisfies(m, "w1", p("P → Q"))
    # w1 ⊨ P → (P → Q): the sole triple needs w1 ⊨ P ⇒ w0 ⊨ P→Q — checked above.
    assert rel_satisfies(m, "w1", p("P → (P → Q)"))
    # So w1 witnesses the failure of contraction at the normal w0.
    assert not rel_satisfies(m, "w0", p("(P → (P → Q)) → (P → Q)"))


def test_lem_countermodel_shape():
    # One world behaves classically (identity star is the only involution on a
    # singleton and R must be empty), so LEM survives at max_worlds=1 ...
    assert rel_countermodel(p("P ∨ ¬P"), max_worlds=1) is None
    # ... and every 2-world refuter must send w0 to a P-world by the star:
    # w0 ⊭ P ∨ ¬P forces w0 ⊭ P and (¬-clause) w0* ⊨ P.
    model, world = rel_countermodel(p("P ∨ ¬P"), max_worlds=2)
    assert world == "w0" and len(model.worlds) == 2
    assert not rel_satisfies(model, "w0", p("P"))
    assert rel_satisfies(model, model.star["w0"], p("P"))


# ---------------------------------------------------------------------------
# Property test: a classical countermodel IS a 1-world simplified RM model.
# ---------------------------------------------------------------------------

_ATOMS = ["P", "Q", "R"]
_BINARY = {"and": And, "or": Or, "implies": Implies, "iff": Iff}


def _rand_prop(rng, depth):
    """A random propositional formula over P/Q/R with ¬ ∧ ∨ → ↔, depth ≤ depth."""
    if depth <= 0 or rng.random() < 0.3:
        return Atom(rng.choice(_ATOMS), [])
    kind = rng.choice(["not", "and", "or", "implies", "iff"])
    if kind == "not":
        return Not(_rand_prop(rng, depth - 1))
    return _BINARY[kind](_rand_prop(rng, depth - 1), _rand_prop(rng, depth - 1))


def test_one_world_search_is_classical():
    """rel_countermodel(φ, 1) succeeds exactly when Z3 finds φ classically invalid.

    A 1-world interpretation has W = N = {w0}, star the identity (the only
    involution on a singleton) and R = ∅ (there are no non-normal source
    worlds), so ¬ collapses to classical negation and the normal-world →-clause
    to material implication over the single world: the 1-world interpretations
    are EXACTLY the classical valuations. Hence Z3-invalid ⇒ a 1-world RM
    countermodel exists (the soundness inclusion B ⊆ CL made executable), and
    conversely Z3-valid ⇒ no 1-world countermodel.
    """
    rng = random.Random(20260703)
    for _ in range(150):
        formula = _rand_prop(rng, 4)
        result = rel_countermodel(formula, max_worlds=1)
        if is_valid(formula):
            assert result is None, formula.to_unicode_str()
        else:
            assert result is not None, formula.to_unicode_str()
            model, world = result
            assert model.worlds == ("w0",) and world in model.normal
            assert not rel_satisfies(model, world, formula)


# ---------------------------------------------------------------------------
# Model validation and input rejection
# ---------------------------------------------------------------------------

def test_model_validation():
    with pytest.raises(ValueError):        # N must be nonempty
        RelevantModel(("w0",), set())
    with pytest.raises(ValueError):        # N ⊆ W
        RelevantModel(("w0",), {"w9"})
    with pytest.raises(ValueError):        # star must be total on W
        RelevantModel(("w0", "w1"), {"w0"}, star={"w0": "w0"})
    with pytest.raises(ValueError):        # star must map into W
        RelevantModel(("w0",), {"w0"}, star={"w0": "w9"})
    with pytest.raises(ValueError):        # star must be an involution: w0* = w1
        RelevantModel(("w0", "w1"), {"w0"},  # but w1* = w1 ≠ w0
                      star={"w0": "w1", "w1": "w1"})
    with pytest.raises(ValueError):        # R sourced at a NORMAL world
        RelevantModel(("w0", "w1"), {"w0"}, R={("w0", "w1", "w1")})
    with pytest.raises(ValueError):        # R mentions an unknown world
        RelevantModel(("w0", "w1"), {"w0"}, R={("w1", "w2", "w0")})
    with pytest.raises(ValueError):        # valuation mentions an unknown world
        RelevantModel(("w0",), {"w0"}, valuation={"P": {"w7"}})


def test_model_ergonomics_and_freezing():
    # Plain lists/sets/dicts go in; frozen, hashable structures come out.
    m = RelevantModel(["w0", "w1"], {"w0"}, star={"w0": "w1", "w1": "w0"},
                      R=[("w1", "w0", "w0")], valuation={"P": ["w1"]})
    assert m.worlds == ("w0", "w1")
    assert m.normal == frozenset({"w0"})
    assert m.star["w0"] == "w1" and dict(m.star) == {"w0": "w1", "w1": "w0"}
    assert m.R == frozenset({("w1", "w0", "w0")})
    assert m.valuation["P"] == frozenset({"w1"})
    # Equal content ⇒ equal models and equal hashes (insertion order irrelevant).
    same = RelevantModel(("w0", "w1"), frozenset({"w0"}),
                         star={"w1": "w0", "w0": "w1"},
                         R={("w1", "w0", "w0")},
                         valuation={"P": frozenset({"w1"})})
    assert m == same and hash(m) == hash(same)
    with pytest.raises(AttributeError):    # frozen dataclass
        m.worlds = ()


def test_rejects_non_propositional_input():
    m = RelevantModel(("w0",), {"w0"})
    bad_inputs = [
        p("∀x P(x)"),          # quantifier
        Box(Atom("P", ())),    # modality
        p("P(a)"),             # non-nullary atom
    ]
    for bad in bad_inputs:
        with pytest.raises(TypeError):
            rel_satisfies(m, "w0", bad)
        with pytest.raises(TypeError):
            rel_countermodel(bad)
        with pytest.raises(TypeError):
            rel_valid(bad)
    with pytest.raises(TypeError):         # not a Node at all
        rel_valid("P → P")
    with pytest.raises(ValueError):        # unknown world
        rel_satisfies(m, "nope", p("P"))
