"""Tests for deontic logic (Standard Deontic Logic, the modal system KD).

Covers the two deontic operators Obligatory O (Ⓞ) and Permitted P (Ⓟ) added to
the modal subsystem:

- parse / Unicode round-trip / to_dict round-trip / LaTeX glyphs / tree labels /
  export rejection, mirroring tests/test_modal_parse.py;
- the Kripke semantics: on a SERIAL "deontic" frame the D axiom ``Oφ → Pφ`` and
  the deontic-K axiom ``O(φ→ψ) → (Oφ→Oψ)`` hold at every world, while factivity
  ``Oφ → φ`` is NOT valid (deontic accessibility need not be reflexive — "ought"
  does not imply "is");
- a translation-soundness cross-check ``satisfies_modal == satisfies(ST)`` over
  random finite Kripke models whose "deontic" relation is serial, mirroring
  tests/test_modal_translation.py.
"""

import random

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.modal_translation import standard_translation
from unicode_fol_kit.fol.nodes import (
    Node,
    Atom, Variable, Constant,
    And, Or, Xor, Not, Implies, Iff, Quantifier,
    Box, Diamond,
    Obligatory, Permitted,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.semantics.tarski import Structure, satisfies


P = Atom("P", [])
Q = Atom("Q", [])
R = Atom("R", [])
PX = Atom("P", [Variable("x")])


@pytest.fixture
def parser():
    return MSFLParser(modal=True)


# ---------------------------------------------------------------------------
# AST shape for each operator, mixed with classical connectives and nesting
# ---------------------------------------------------------------------------

# (source string, expected AST)
PARSE_CASES = [
    ("ⓄP", Obligatory(P)),
    ("ⓅP", Permitted(P)),
    # nesting
    ("ⓄⓄP", Obligatory(Obligatory(P))),
    ("ⓄⓅP", Obligatory(Permitted(P))),
    ("ⓅⓄP", Permitted(Obligatory(P))),
    ("Ⓞ¬P", Obligatory(Not(P))),
    ("¬ⓄP", Not(Obligatory(P))),
    # the derived prohibition Fφ ≡ O¬φ ≡ ¬Pφ
    ("Ⓞ¬P", Obligatory(Not(P))),
    ("¬ⓅP", Not(Permitted(P))),
    # mixing with classical connectives
    ("ⓄP ∧ Q", And(Obligatory(P), Q)),
    ("Ⓞ(P ∧ Q)", Obligatory(And(P, Q))),
    ("ⓅP ∨ ⓅQ", Or(Permitted(P), Permitted(Q))),
    ("ⓄP → ⓅP", Implies(Obligatory(P), Permitted(P))),       # the D axiom shape
    ("ⓄP ↔ ¬Ⓟ¬P", Iff(Obligatory(P), Not(Permitted(Not(P))))),
    ("ⓄP ⊕ Q", Xor(Obligatory(P), Q)),
    ("Ⓞ(P → Q) → (ⓄP → ⓄQ)",
     Implies(Obligatory(Implies(P, Q)),
             Implies(Obligatory(P), Obligatory(Q)))),       # deontic-K shape
    # mixing deontic with the other modal operators
    ("Ⓞ□P", Obligatory(Box(P))),
    ("□ⓄP", Box(Obligatory(P))),
    ("Ⓟ◇P", Permitted(Diamond(P))),
    # with quantifiers
    ("∀x ⓄP(x)", Quantifier("∀", Variable("x"), Obligatory(PX))),
    ("Ⓞ∀x P(x)", Obligatory(Quantifier("∀", Variable("x"), PX))),
    ("∃x ⓅP(x)", Quantifier("∃", Variable("x"), Permitted(PX))),
]


class TestParseShape:
    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_parse(self, parser, src, expected):
        assert parser.parse(src) == expected


# ---------------------------------------------------------------------------
# Unicode parser round-trip: parse(ast.to_unicode_str()) == ast
# ---------------------------------------------------------------------------

class TestUnicodeRoundTrip:
    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_round_trip(self, parser, src, expected):
        ast = parser.parse(src)
        assert parser.parse(ast.to_unicode_str()) == ast

    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_round_trip_equals_expected(self, parser, src, expected):
        assert parser.parse(expected.to_unicode_str()) == expected

    def test_obligatory_glyph(self):
        assert Obligatory(P).to_unicode_str() == "ⓄP"

    def test_permitted_glyph(self):
        assert Permitted(P).to_unicode_str() == "ⓅP"

    def test_obligatory_parenthesises_binary_body(self):
        assert Obligatory(And(P, Q)).to_unicode_str() == "Ⓞ(P ∧ Q)"


# ---------------------------------------------------------------------------
# to_dict / from_dict round-trip
# ---------------------------------------------------------------------------

class TestDictRoundTrip:
    @pytest.mark.parametrize("src,expected", PARSE_CASES)
    def test_dict_round_trip(self, expected, src):
        assert Node.from_dict(expected.to_dict()) == expected

    def test_obligatory_dict(self):
        d = Obligatory(P).to_dict()
        assert d == {"_type": "Obligatory", "formula": P.to_dict()}

    def test_permitted_dict(self):
        d = Permitted(Q).to_dict()
        assert d == {"_type": "Permitted", "formula": Q.to_dict()}

    @pytest.mark.parametrize("node", [
        Obligatory(P), Permitted(P),
        Obligatory(Permitted(Q)), Permitted(Obligatory(And(P, Q))),
    ])
    def test_each_node_dict_round_trip(self, node):
        assert Node.from_dict(node.to_dict()) == node


# ---------------------------------------------------------------------------
# LaTeX glyphs
# ---------------------------------------------------------------------------

class TestLatex:
    @pytest.mark.parametrize("node,expected", [
        (Obligatory(P), "\\mathsf{O} P"),
        (Permitted(P), "\\mathsf{P} P"),
        (Obligatory(Q), "\\mathsf{O} Q"),
        (Permitted(Q), "\\mathsf{P} Q"),
    ])
    def test_latex_glyphs(self, node, expected):
        assert node.to_latex() == expected

    def test_latex_nested(self):
        assert Obligatory(Permitted(P)).to_latex() == "\\mathsf{O} \\mathsf{P} P"

    def test_latex_obligatory_implies_permitted(self):
        assert (Implies(Obligatory(P), Permitted(P)).to_latex()
                == "\\mathsf{O} P \\rightarrow \\mathsf{P} P")

    def test_latex_obligatory_and(self, parser):
        ast = parser.parse("ⓄP ∧ Q")
        assert ast.to_latex() == "\\mathsf{O} P \\land Q"

    def test_latex_obligatory_parenthesises_conjunction(self):
        assert Obligatory(And(P, Q)).to_latex() == "\\mathsf{O} (P \\land Q)"


# ---------------------------------------------------------------------------
# tree_str labels
# ---------------------------------------------------------------------------

class TestTreeStr:
    def test_obligatory_tree(self):
        s = Obligatory(P).tree_str()
        assert s.startswith("Ⓞ")
        assert "Atom: P" in s

    def test_permitted_tree(self):
        s = Permitted(Q).tree_str()
        assert s.startswith("Ⓟ")
        assert "Atom: Q" in s


# ---------------------------------------------------------------------------
# Export rejection: to_z3 / to_prover9 / to_tptp raise NotImplementedError
# ---------------------------------------------------------------------------

DEONTIC_NODES = [Obligatory(P), Permitted(P), Obligatory(Permitted(Q))]


class TestExportRejection:
    @pytest.mark.parametrize("node", DEONTIC_NODES)
    def test_to_z3_raises(self, node):
        with pytest.raises(NotImplementedError):
            node.to_z3()

    @pytest.mark.parametrize("node", DEONTIC_NODES)
    def test_to_prover9_raises(self, node):
        with pytest.raises(NotImplementedError):
            node.to_prover9()

    @pytest.mark.parametrize("node", DEONTIC_NODES)
    def test_to_tptp_raises(self, node):
        with pytest.raises(NotImplementedError):
            node.to_tptp()


# ---------------------------------------------------------------------------
# Structural inheritance: free_variables / traversal recurse into deontic nodes
# ---------------------------------------------------------------------------

class TestStructural:
    def test_free_variables_through_obligatory(self):
        from unicode_fol_kit.fol.nodes import free_variables
        assert free_variables(Obligatory(PX)) == {Variable("x")}

    def test_free_variables_bound_under_deontic(self):
        from unicode_fol_kit.fol.nodes import free_variables
        node = Obligatory(Quantifier("∀", Variable("x"), PX))
        assert free_variables(node) == set()

    def test_walk_visits_deontic_children(self):
        node = Obligatory(And(P, Q))
        kinds = [type(n).__name__ for n in node.walk()]
        assert kinds[0] == "Obligatory"
        assert "And" in kinds and kinds.count("Atom") == 2

    def test_depth_counts_deontic_layer(self):
        assert Obligatory(P).depth() == 2
        assert Obligatory(Permitted(P)).depth() == 3


# ---------------------------------------------------------------------------
# Translation shape
# ---------------------------------------------------------------------------

class TestTranslationShape:
    def test_obligatory_translation_shape(self):
        """Obligatory φ -> ∀w0 (D(w, w0) -> ST(φ, w0))."""
        st = standard_translation(Obligatory(P), "w")
        expected = Quantifier(
            "∀", Variable("w0"),
            Implies(Atom("D", [Variable("w"), Variable("w0")]),
                    Atom("P", [Variable("w0")])),
        )
        assert st == expected

    def test_permitted_translation_shape(self):
        """Permitted φ -> ∃w0 (D(w, w0) ∧ ST(φ, w0))."""
        st = standard_translation(Permitted(P), "w")
        expected = Quantifier(
            "∃", Variable("w0"),
            And(Atom("D", [Variable("w"), Variable("w0")]),
                Atom("P", [Variable("w0")])),
        )
        assert st == expected

    def test_deontic_predicate_name(self):
        st = standard_translation(Obligatory(P), "w")
        assert st.formula.left == Atom("D", [Variable("w"), Variable("w0")])

    def test_translation_is_plain_fol_and_exportable(self):
        """The translated deontic formula is plain FOL the back-ends accept."""
        st = standard_translation(Implies(Obligatory(Implies(P, Q)),
                                          Implies(Obligatory(P), Obligatory(Q))), "w")
        st.to_z3()
        st.to_prover9()
        st.to_tptp()


# ---------------------------------------------------------------------------
# Kripke validities on a serial frame
# ---------------------------------------------------------------------------

def _make_serial_relation(worlds, edges):
    """Return ``edges`` augmented to be SERIAL over ``worlds``.

    Seriality (every world has at least one deontic successor) is the frame
    condition characterising the D axiom of Standard Deontic Logic. Any world
    with no outgoing edge in ``edges`` gets a self-loop so the result is serial
    without adding fresh worlds.
    """
    edges = set(edges)
    have_succ = {a for (a, _b) in edges}
    for w in worlds:
        if w not in have_succ:
            edges.add((w, w))
    return edges


# Atomic-letter formulas used to instantiate the deontic schemata.
_SCHEMA_PARTS = [P, Q, Not(P), And(P, Q), Or(P, Q), Implies(P, Q)]


class TestKripkeValidities:
    def _random_serial_models(self, rng, n_models=40):
        """Yield random Kripke models whose "deontic" relation is serial."""
        for _ in range(n_models):
            n_worlds = rng.randint(1, 4)
            worlds = list(range(n_worlds))
            raw = {(a, b) for a in worlds for b in worlds if rng.random() < 0.4}
            deontic = _make_serial_relation(worlds, raw)
            valuation = {w: {a for a in ("P", "Q") if rng.random() < 0.5}
                         for w in worlds}
            yield KripkeModel(worlds=worlds,
                              relations={"deontic": deontic},
                              valuation=valuation)

    def test_d_axiom_holds_on_serial_frames(self):
        """On every serial deontic frame, Oφ → Pφ holds at every world."""
        rng = random.Random(424242)
        for model in self._random_serial_models(rng):
            for phi in _SCHEMA_PARTS:
                d_axiom = Implies(Obligatory(phi), Permitted(phi))
                for w in model.worlds:
                    assert satisfies_modal(d_axiom, model, w), (
                        f"D axiom failed for {phi.to_unicode_str()} at world {w}"
                    )

    def test_deontic_k_axiom_holds(self):
        """The K axiom O(φ→ψ) → (Oφ→Oψ) holds at every world (any frame, K is the base).

        K is valid on every Kripke frame, serial or not — it is the base axiom of
        the normal modal logic underlying SDL; we still drive it on serial frames
        for thematic consistency.
        """
        rng = random.Random(99)
        for model in self._random_serial_models(rng):
            for phi in _SCHEMA_PARTS:
                for psi in _SCHEMA_PARTS:
                    k_axiom = Implies(
                        Obligatory(Implies(phi, psi)),
                        Implies(Obligatory(phi), Obligatory(psi)),
                    )
                    for w in model.worlds:
                        assert satisfies_modal(k_axiom, model, w), (
                            f"K axiom failed at world {w} for "
                            f"{phi.to_unicode_str()}, {psi.to_unicode_str()}"
                        )

    def test_d_axiom_concrete(self):
        """A concrete serial frame where Oφ and Pφ both hold."""
        model = KripkeModel(
            worlds={0, 1},
            relations={"deontic": {(0, 1), (1, 1)}},
            valuation={1: {"P"}},
        )
        assert satisfies_modal(Obligatory(P), model, 0)
        assert satisfies_modal(Permitted(P), model, 0)
        assert satisfies_modal(Implies(Obligatory(P), Permitted(P)), model, 0)

    def test_factivity_not_valid_ought_does_not_imply_is(self):
        """Oφ → φ is NOT valid: a serial frame with Oφ true but φ false at the actual world.

        Deontic accessibility need not be reflexive — what is obligatory need not
        actually be the case. World 0 (the actual world) sees only world 1, where
        P holds, so Oφ is true at 0; but P is FALSE at 0 itself, so Oφ → φ fails
        there. The frame is serial (0→1, 1→1), so this is a genuine SDL model.
        """
        model = KripkeModel(
            worlds={0, 1},
            relations={"deontic": {(0, 1), (1, 1)}},
            valuation={1: {"P"}},        # P true only at world 1, NOT at actual world 0
        )
        assert satisfies_modal(Obligatory(P), model, 0) is True
        assert satisfies_modal(P, model, 0) is False
        # Hence factivity Oφ → φ is false at the actual world 0.
        assert satisfies_modal(Implies(Obligatory(P), P), model, 0) is False


# ---------------------------------------------------------------------------
# Translation soundness cross-check (serial deontic frames)
# ---------------------------------------------------------------------------

# Deontic formulas in the translatable propositional fragment.
_TRANSLATABLE_DEONTIC = [
    P,
    Obligatory(P),
    Permitted(P),
    Not(Obligatory(P)),
    Obligatory(Not(P)),
    Implies(Obligatory(P), Permitted(P)),                 # D axiom
    Implies(Obligatory(Implies(P, Q)),
            Implies(Obligatory(P), Obligatory(Q))),       # K axiom
    Obligatory(And(P, Q)),
    Permitted(Or(P, Q)),
    Obligatory(Obligatory(P)),                            # nested (fresh-world capture)
    Obligatory(Permitted(P)),
    Permitted(Obligatory(Q)),
    And(Obligatory(P), Permitted(Q)),
    Iff(Permitted(P), Not(Obligatory(Not(P)))),           # P ≡ ¬O¬ duality
]


def _structure_from_deontic_model(model, atom_names):
    """Build the FOL Structure matching a deontic Kripke model.

    The "deontic" relation becomes the binary predicate ``D``; each propositional
    atom ``A`` becomes a unary predicate whose extension is the worlds where A is
    true. Mirrors the construction in tests/test_modal_translation.py.
    """
    predicates = {}
    predicates[("D", 2)] = set(model.relation("deontic"))
    for name in atom_names:
        predicates[(name, 1)] = {(w,) for w in model.worlds
                                 if name in model.atoms_true_at(w)}
    return Structure(domain=set(model.worlds), predicates=predicates)


def test_translation_soundness_cross_check():
    """satisfies_modal(φ, model, w) == satisfies(ST(φ), structure, {w↦w}) everywhere.

    Over many random Kripke models whose "deontic" relation is serial, every
    translatable deontic formula has the same Kripke truth at every world as the
    Tarski truth of its standard translation (mapping "deontic" to the predicate
    ``D``). Seriality is not required for this correspondence — the standard
    translation is sound on any frame — but the frames are serial here to stay
    faithful to Standard Deontic Logic.
    """
    rng = random.Random(20260623)
    atom_names = ["P", "Q"]
    for _ in range(120):
        n_worlds = rng.randint(1, 4)
        worlds = list(range(n_worlds))
        raw = {(a, b) for a in worlds for b in worlds if rng.random() < 0.45}
        deontic = _make_serial_relation(worlds, raw)
        valuation = {w: {a for a in atom_names if rng.random() < 0.5} for w in worlds}
        model = KripkeModel(worlds=worlds,
                            relations={"deontic": deontic},
                            valuation=valuation)
        structure = _structure_from_deontic_model(model, atom_names)
        for formula in _TRANSLATABLE_DEONTIC:
            translated = standard_translation(formula, "w")
            for w in model.worlds:
                kripke_truth = satisfies_modal(formula, model, w)
                tarski_truth = satisfies(translated, structure, {"w": w})
                assert kripke_truth == tarski_truth, (
                    f"mismatch for {formula.to_unicode_str()} at world {w}: "
                    f"kripke={kripke_truth} tarski={tarski_truth}; "
                    f"ST={translated.to_unicode_str()}"
                )
