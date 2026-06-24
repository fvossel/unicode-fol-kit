"""Tests for the standard translation, fol/modal_translation.py.

The headline test is a SOUNDNESS cross-check: for many propositional modal
formulas (box / diamond / knows / believes / always / eventually / next, no
Until or quantifiers) and many random finite Kripke models, build the
corresponding first-order :class:`Structure` and assert that the Kripke truth of
φ at every world equals the Tarski truth of ``standard_translation(φ)`` in that
structure with the world variable bound to the same world.
"""

import random

import pytest

from unicode_fol_kit.fol.modal_translation import standard_translation
from unicode_fol_kit.fol.nodes import (
    Atom, Constant, Variable, Not, And, Or, Implies, Iff, Xor,
    Box, Diamond, Knows, Believes,
    Always, Eventually, Next, Until,
    Quantifier, SortedQuantifier,
    LukNegation, Lambda, LambdaVar,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.semantics.tarski import Structure, satisfies

P = Atom("P", [])
Q = Atom("Q", [])

# Accessibility-predicate names produced by the standard translation, paired
# with the Kripke relation-name they correspond to. Kept in sync with the
# modal_translation module docstring.
_REL_MAP = {
    "alethic": "R",
    "K:alice": "Rk_alice",
    "K:bob": "Rk_bob",
    "B:alice": "Rb_alice",
    "temporal": "T",  # Always/Eventually translate as box/diamond over T
    "next": "N",      # the one-step Next predicate
}


def _structure_from_kripke(model, atom_names):
    """Build the FOL Structure matching a Kripke model for the soundness check.

    - domain = the worlds.
    - each accessibility relation becomes a binary predicate (R / Rk_a / Rb_a /
      T / N) whose extension is the relation's edge set.
    - each propositional atom ``A`` becomes a unary predicate ``A`` whose
      extension is ``{(w,) for w where A is true}``.

    ``atom_names`` lists the propositional atom names to lift into unary
    predicates. The "temporal" relation is mapped to BOTH ``T`` (for
    Always/Eventually) and ``N`` (for Next), since the standard translation uses
    distinct predicate names but the Kripke model uses the single "temporal"
    relation as the accessibility for all of them in this check. In the
    cross-check the "temporal" relation is a preorder (reflexive-transitive), so
    the Kripke closure reading of Always/Eventually coincides with the box/
    diamond translation over ``T``.
    """
    predicates = {}

    # Binary accessibility predicates from the relations.
    for rel_name, edges in model.relations.items():
        if rel_name == "temporal":
            predicates[("T", 2)] = set(edges)
            predicates[("N", 2)] = set(edges)
        else:
            fol_name = _REL_MAP.get(rel_name)
            if fol_name is not None:
                predicates[(fol_name, 2)] = set(edges)

    # Unary atom predicates from the valuation.
    for name in atom_names:
        ext = {(w,) for w in model.worlds if name in model.atoms_true_at(w)}
        predicates[(name, 1)] = ext

    return Structure(domain=set(model.worlds), predicates=predicates)


def _preorder_closure(edges, worlds):
    """Return the reflexive-transitive closure of ``edges`` over ``worlds``.

    Used so the random ``"temporal"`` relation is a preorder. On a preorder the
    Kripke reflexive-transitive-closure reading of Always/Eventually coincides
    with the standard translation's one-step box/diamond over ``T`` — that
    coincidence is precisely what makes the soundness cross-check meaningful for
    the temporal operators (see the modal_translation module docstring).
    """
    closure = set(edges) | {(w, w) for w in worlds}
    changed = True
    while changed:
        changed = False
        new = {(a, c) for (a, b) in closure for (b2, c) in closure if b == b2}
        if not new <= closure:
            closure |= new
            changed = True
    return closure


def _random_model(rng, relation_names, atom_names, n_worlds):
    """Build a random Kripke model over the given relations and atoms.

    The ``"temporal"`` relation is closed into a reflexive-transitive preorder
    (see :func:`_preorder_closure`); the other accessibility relations are
    arbitrary.
    """
    worlds = list(range(n_worlds))
    relations = {}
    for rname in relation_names:
        edges = {(a, b) for a in worlds for b in worlds if rng.random() < 0.45}
        if rname == "temporal":
            edges = _preorder_closure(edges, worlds)
        relations[rname] = edges
    valuation = {}
    for w in worlds:
        true_here = {a for a in atom_names if rng.random() < 0.5}
        valuation[w] = true_here
    return KripkeModel(worlds=worlds, relations=relations, valuation=valuation)


# Propositional modal formulas in the translatable fragment (no Until / quants).
_TRANSLATABLE_FORMULAS = [
    P,
    Not(P),
    And(P, Q),
    Or(P, Q),
    Implies(P, Q),
    Iff(P, Q),
    Xor(P, Q),
    Box(P),
    Diamond(P),
    Box(Implies(P, Q)),
    Implies(Box(P), Box(Q)),
    Diamond(And(P, Q)),
    Box(Box(P)),                       # nested boxes (fresh-var capture check)
    Box(Diamond(P)),
    Diamond(Box(Q)),
    Knows("alice", P),
    Believes("alice", Q),
    Knows("alice", Knows("bob", P)),   # nested distinct epistemic relations
    And(Knows("alice", P), Box(Q)),
    Next(P),
    Always(P),
    Eventually(Q),
    Next(Always(P)),
    Implies(Always(P), Eventually(P)),
    Box(Implies(P, Diamond(Q))),
]


def test_soundness_cross_check():
    """satisfies_modal(φ, model, w) == satisfies(ST(φ), structure, {w↦w}) everywhere.

    Over many random Kripke models, for every translatable formula and every
    world, the Kripke truth equals the Tarski truth of the standard translation.
    This is the key correctness theorem for the standard translation. The
    temporal relation is generated as a preorder so the closure-based Kripke
    reading of Always/Eventually matches their one-step box/diamond translation
    over ``T`` (the documented divergence vanishes on a reflexive-transitive
    frame).
    """
    rng = random.Random(20240623)
    relation_names = ["alethic", "K:alice", "K:bob", "B:alice", "temporal"]
    atom_names = ["P", "Q"]

    for _ in range(120):
        n_worlds = rng.randint(1, 4)
        model = _random_model(rng, relation_names, atom_names, n_worlds)
        structure = _structure_from_kripke(model, atom_names)
        for formula in _TRANSLATABLE_FORMULAS:
            translated = standard_translation(formula, "w")
            for w in model.worlds:
                kripke_truth = satisfies_modal(formula, model, w)
                tarski_truth = satisfies(translated, structure, {"w": w})
                assert kripke_truth == tarski_truth, (
                    f"mismatch for {formula.to_unicode_str()} at world {w}: "
                    f"kripke={kripke_truth} tarski={tarski_truth}; "
                    f"ST={translated.to_unicode_str()}"
                )


# ---------------------------------------------------------------------------
# Shape of the translation output
# ---------------------------------------------------------------------------

def test_atom_gets_world_argument():
    """A propositional atom A becomes A(w)."""
    st = standard_translation(P, "w")
    assert st == Atom("P", [Variable("w")])


def test_atom_with_args_appends_world():
    """A ground atom keeps its arguments and gains the world as the last arg."""
    likes = Atom("Likes", [Constant("a"), Constant("b")])
    st = standard_translation(likes, "w")
    assert st == Atom("Likes", [Constant("a"), Constant("b"), Variable("w")])


def test_box_translation_shape():
    """Box φ -> ∀w0 (R(w, w0) -> ST(φ, w0))."""
    st = standard_translation(Box(P), "w")
    expected = Quantifier(
        "∀", Variable("w0"),
        Implies(Atom("R", [Variable("w"), Variable("w0")]),
                Atom("P", [Variable("w0")])),
    )
    assert st == expected


def test_diamond_translation_shape():
    """Diamond φ -> ∃w0 (R(w, w0) ∧ ST(φ, w0))."""
    st = standard_translation(Diamond(P), "w")
    expected = Quantifier(
        "∃", Variable("w0"),
        And(Atom("R", [Variable("w"), Variable("w0")]),
            Atom("P", [Variable("w0")])),
    )
    assert st == expected


def test_knows_and_believes_predicate_names():
    """Knows uses Rk_<agent>, Believes uses Rb_<agent>."""
    st_k = standard_translation(Knows("alice", P), "w")
    assert st_k.formula.left == Atom("Rk_alice", [Variable("w"), Variable("w0")])
    st_b = standard_translation(Believes("bob", P), "w")
    assert st_b.formula.left == Atom("Rb_bob", [Variable("w"), Variable("w0")])


def test_temporal_predicate_names():
    """Always/Eventually use T; Next uses N."""
    st_g = standard_translation(Always(P), "w")
    assert st_g.formula.left == Atom("T", [Variable("w"), Variable("w0")])
    st_f = standard_translation(Eventually(P), "w")
    assert st_f.formula.left == Atom("T", [Variable("w"), Variable("w0")])
    st_x = standard_translation(Next(P), "w")
    assert st_x.formula.left == Atom("N", [Variable("w"), Variable("w0")])


def test_nested_modalities_use_fresh_worlds():
    """Nested boxes introduce distinct fresh world variables (no capture)."""
    st = standard_translation(Box(Box(P)), "w")
    # ∀w0 (R(w,w0) -> ∀w1 (R(w0,w1) -> P(w1)))
    outer = st
    assert outer.variable == Variable("w0")
    inner = outer.formula.right
    assert inner.variable == Variable("w1")
    assert inner.formula.right == Atom("P", [Variable("w1")])


def test_custom_world_name():
    """The world argument honours the supplied name."""
    st = standard_translation(P, "s")
    assert st == Atom("P", [Variable("s")])


def test_world_name_in_fresh_namespace_is_not_captured():
    """A current-world name like ``w0`` must not be captured by a bound world var.

    The fresh-world generator emits ``w0, w1, …``; if the caller passes
    ``world="w0"`` the free current-world variable would clash with the first
    fresh name unless the generator skips it. Box(P) translated at ``w0`` must
    keep ``w0`` free in the accessibility atom and bind a DISTINCT fresh
    variable.
    """
    st = standard_translation(Box(P), "w0")
    # Expect ∀w1 (R(w0, w1) -> P(w1)); the bound var is w1, NOT w0.
    assert st.variable == Variable("w1")
    assert st.formula.left == Atom("R", [Variable("w0"), Variable("w1")])
    assert st.formula.right == Atom("P", [Variable("w1")])
    # And nested modalities keep skipping the reserved name.
    st2 = standard_translation(Box(Box(P)), "w1")
    assert st2.variable == Variable("w0")
    assert st2.formula.right.variable == Variable("w2")


def test_capture_free_world_name_soundness():
    """The non-default world name keeps the translation sound (no capture flip).

    Regression: with ``world="w0"`` the free world variable was captured, making
    the translated truth independent of the start world. Cross-check against the
    Kripke evaluator on a frame where Box(P) is false at the start world.
    """
    model = KripkeModel(
        worlds={0, 1},
        relations={"alethic": {(0, 1)}},
        valuation={0: set(), 1: set()},
    )
    structure = Structure(domain={0, 1}, predicates={("R", 2): {(0, 1)}, ("P", 1): set()})
    st = standard_translation(Box(P), "w0")
    for w in (0, 1):
        kripke_truth = satisfies_modal(Box(P), model, w)
        tarski_truth = satisfies(st, structure, {"w0": w})
        assert kripke_truth == tarski_truth


def test_translation_is_exportable_to_z3_and_tptp():
    """The translated formula is plain FOL, so the FOL back-ends accept it."""
    st = standard_translation(Box(Implies(P, Q)), "w")
    # Should not raise.
    st.to_z3()
    st.to_prover9()
    st.to_tptp()


# ---------------------------------------------------------------------------
# Rejections
# ---------------------------------------------------------------------------

def test_until_rejected():
    """standard_translation(Until(...)) raises NotImplementedError."""
    with pytest.raises(NotImplementedError):
        standard_translation(Until(P, Q))


def test_nested_until_rejected():
    """An Until nested under a modality is still rejected."""
    with pytest.raises(NotImplementedError):
        standard_translation(Box(Until(P, Q)))


def test_quantifier_rejected():
    """An object-level quantifier raises NotImplementedError."""
    f = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    with pytest.raises(NotImplementedError):
        standard_translation(f)


def test_quantifier_under_modality_rejected():
    """A quantifier nested under a box is rejected too."""
    f = Box(Quantifier("∃", Variable("x"), Atom("P", [Variable("x")])))
    with pytest.raises(NotImplementedError):
        standard_translation(f)


def test_sorted_quantifier_rejected():
    """A sorted quantifier raises NotImplementedError."""
    f = SortedQuantifier("∀", Variable("x"), "nat", Atom("P", [Variable("x")]))
    with pytest.raises(NotImplementedError):
        standard_translation(f)


def test_fuzzy_rejected():
    """A Łukasiewicz node raises NotImplementedError."""
    with pytest.raises(NotImplementedError):
        standard_translation(LukNegation(P))


def test_lambda_rejected():
    """A lambda node raises NotImplementedError."""
    with pytest.raises(NotImplementedError):
        standard_translation(Lambda(LambdaVar("x"), P))
