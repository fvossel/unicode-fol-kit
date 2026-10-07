"""The glyphs ``⊤`` and ``⊥`` are the two truth constants in every unicode grammar.

``⊤`` is the nullary atom ``$true`` and ``⊥`` the nullary atom ``$false`` (the
atoms the TPTP, QMLTP and SMT-LIB readers already produce). Every grammar mode
that has propositional atoms reads the two glyphs to those atoms and prints them
back as the same glyphs, so ``parse(print(f)) == f`` holds for a formula that uses
them. Two modes keep their own meaning: in the linear grammar ``⊤`` is the additive
truth of linear logic, and the Lambek grammar has no propositional constants at
all.
"""

import pytest

from unicode_logic_kit.fol._fol_nodes import Atom
from unicode_logic_kit.fol.latex_input import parse_latex
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.naming import NamingError
from unicode_logic_kit.fol.nodes import (
    Constant, And, Or, Not, Implies, Box, Diamond, Quantifier, Variable,
)

T = Atom("$true", ())
F = Atom("$false", ())
P = Atom("P", ())

#: every grammar mode that has propositional atoms, as MSFLParser keywords
MODES = {
    "fol": {},
    "msfol": {"many_sorted": True},
    "msfl": {"many_sorted": True, "fuzzy": True},
    "fl": {"fuzzy": True},
    "modal": {"modal": True},
    "modal_sorted": {"modal": True, "many_sorted": True},
    "so": {"second_order": True},
    "so_sorted": {"second_order": True, "many_sorted": True},
    "to": {"third_order": True},
    "tomodal": {"third_order": True, "modal": True},
    "dependence": {"dependence": True},
}
MODE_IDS = sorted(MODES)


def parser(mode):
    return MSFLParser(**MODES[mode])


# ---------------------------------------------------------------------------
# The glyphs read to the two atoms, in every mode
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("mode", MODE_IDS)
def test_top_glyph_is_the_true_constant(mode):
    assert parser(mode).parse("⊤") == T


@pytest.mark.parametrize("mode", MODE_IDS)
def test_bottom_glyph_is_the_false_constant(mode):
    assert parser(mode).parse("⊥") == F


@pytest.mark.parametrize("mode", MODE_IDS)
def test_glyphs_inside_a_formula(mode):
    # (⊤ ∧ P) ∨ ¬⊥ : the constants sit under the connectives like any atom (the
    # dependence grammar has no arrows, so the connectives here are ∧ ∨ ¬ only)
    tree = parser(mode).parse("(⊤ ∧ P) ∨ ¬⊥")
    atoms = [n for n in tree.walk() if isinstance(n, Atom)]
    assert sorted(a.predicate for a in atoms) == ["$false", "$true", "P"]


def test_glyph_forms_in_the_classical_grammar_are_exact_trees():
    # hand-built: (⊤ ∧ P) → ¬⊥
    assert parser("fol").parse("⊤ ∧ P → ¬⊥") == Implies(And(T, P), Not(F))
    # hand-built: ⊤ ∨ ⊥
    assert parser("fol").parse("⊤ ∨ ⊥") == Or(T, F)


def test_glyphs_under_modal_operators():
    # □⊤ → ◇¬⊥
    assert parser("modal").parse("□⊤ → ◇¬⊥") == Implies(Box(T), Diamond(Not(F)))


def test_glyphs_under_quantifiers():
    x = Variable("x")
    # ∀x (P → ⊤): the constant is a closed atom, no free variable in it
    tree = parser("fol").parse("∀x (P → ⊤)")
    assert tree == Quantifier("∀", x, Implies(P, T))


# ---------------------------------------------------------------------------
# Printing, and the round trip parse(print(f)) == f
# ---------------------------------------------------------------------------

def test_atoms_print_as_the_glyphs():
    assert T.to_unicode_str() == "⊤"
    assert F.to_unicode_str() == "⊥"


def test_atoms_print_as_latex_commands():
    assert T.to_latex() == r"\top"
    assert F.to_latex() == r"\bot"


FORMULA_TEXTS = [
    "⊤",
    "⊥",
    "⊤ ∧ P",
    "P ∨ ⊥",
    "¬⊥",
    "¬⊤",
    "⊥ → P",
    "P → ⊤",
    "⊤ ↔ ⊥",
    "(⊤ ∧ P) ∨ ¬(P ∧ ⊥)",
]


@pytest.mark.parametrize("mode", MODE_IDS)
@pytest.mark.parametrize("text", FORMULA_TEXTS)
def test_print_then_parse_is_the_identity(mode, text):
    if mode == "dependence" and ("→" in text or "↔" in text):
        pytest.skip("the dependence grammar has no implication or equivalence arrows")
    p = parser(mode)
    tree = p.parse(text)
    assert p.parse(tree.to_unicode_str()) == tree


@pytest.mark.parametrize("mode", [m for m in MODE_IDS if "modal" in m])
def test_print_then_parse_with_modal_operators(mode):
    p = parser(mode)
    for text in ("□⊤", "◇⊥", "□⊤ → ◇¬⊥", "□(P ∨ ⊥) → ⊤"):
        tree = p.parse(text)
        assert p.parse(tree.to_unicode_str()) == tree


@pytest.mark.parametrize("mode", ["fol", "msfol", "modal", "so", "to"])
def test_print_then_parse_with_quantifiers(mode):
    p = parser(mode)
    sort = ":S" if mode == "msfol" else ""      # the many-sorted grammar needs a sort
    for text in (f"∀x{sort} (P(x) → ⊤)", f"∃x{sort} (⊥ ∨ P(x))"):
        tree = p.parse(text)
        assert p.parse(tree.to_unicode_str()) == tree
        assert {a.predicate for a in tree.walk() if isinstance(a, Atom)} >= {"P"}


def test_directly_built_formula_round_trips():
    # an AST built by hand, not parsed, prints to something that reads back to it
    formula = Implies(And(T, P), Not(F))
    assert parser("fol").parse(formula.to_unicode_str()) == formula


@pytest.mark.parametrize("mode", ["fol", "msfol", "fl", "msfl"])
def test_latex_round_trip(mode):
    kwargs = {k: v for k, v in MODES[mode].items() if k in ("many_sorted", "fuzzy")}
    tree = parser(mode).parse("⊤ ∧ P → ¬⊥")
    assert parse_latex(tree.to_latex(), **kwargs) == tree


def test_latex_commands_read_to_the_atoms():
    assert parse_latex(r"\top") == T
    assert parse_latex(r"\bot") == F
    assert parse_latex(r"\top \land P") == And(T, P)


# ---------------------------------------------------------------------------
# The other printers
# ---------------------------------------------------------------------------

def test_prover9_spelling():
    assert And(T, F).to_prover9() == "($T & $F)"


def test_tptp_spelling():
    assert And(T, F).to_tptp() == "($true & $false)"


def test_smtlib_spelling():
    from unicode_logic_kit.atp.z3_input import to_smtlib
    text = to_smtlib(Implies(T, F))
    assert "(=> true false)" in text
    assert "declare-fun" not in text          # a constant declares no symbol


def test_serialization_round_trip():
    from unicode_logic_kit.fol.serialize import serialize, deserialize
    formula = Implies(And(T, P), Not(F))
    assert deserialize(serialize(formula)) == formula


# ---------------------------------------------------------------------------
# The modes whose reading of the glyphs is their own
# ---------------------------------------------------------------------------

def test_linear_grammar_keeps_top_as_the_additive_truth():
    from unicode_logic_kit.fol._linear_nodes import Top
    linear = MSFLParser(linear=True)
    assert isinstance(linear.parse("⊤"), Top)
    with pytest.raises(NamingError):
        linear.parse("⊥")          # the linear grammar has its own units (0, 1, ⊤), no ⊥


def test_dialect_detection_reads_the_glyphs_as_constants_and_keeps_the_linear_markers():
    from unicode_logic_kit.api import parse_any
    # no grammar-specific symbol: the first grammar that reads it, the classical one
    result = parse_any("P ∧ ⊤")
    assert result.ok and result.dialect == "fol"
    assert result.formula == And(P, T)
    result = parse_any("⊥ → P")
    assert result.dialect == "fol" and result.formula == Implies(F, P)
    # a bare ⊤ is the truth constant; the linear unit needs a linear symbol around it
    assert parse_any("⊤").formula == T
    # the linear grammar is still chosen by its own symbols
    from unicode_logic_kit.fol._linear_nodes import Top
    result = parse_any("⊤ ⊸ A")
    assert result.dialect == "linear"
    assert isinstance(result.formula.left, Top)


def test_lambek_grammar_has_no_propositional_constants():
    lambek = MSFLParser(lambek=True)
    for glyph in ("⊤", "⊥"):
        with pytest.raises(NamingError):
            lambek.parse(glyph)
