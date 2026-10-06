"""The truth constants where they are declared, read and said: the signature, the Prover9 and
CASL readers, the repair of a formula, and the two verbalisers.

``$true`` and ``$false`` (and the atoms named ``⊤`` and ``⊥``, which are the same two
constants) are propositions the language defines, not symbols of the user's:

* a signature declares no predicate for them and does not call them undeclared;
* Prover9 writes them ``$T`` and ``$F`` and its reader reads those two words back;
* CASL writes them ``true`` and ``false`` and its reader reads those two words back;
* ``P -> ⊥`` is the Prover9 arrow with the unicode glyph for falsity, and is repaired the way
  ``P -> Q`` is;
* the English verbaliser says "truth" and "falsity", and the ACE verbaliser, whose language
  has no sentence that is true or false by itself, refuses them by name.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, And, Box, Constant, Iff, Implies, Not, Or, Quantifier, Variable,
)
from unicode_fol_kit.fol.signature import Signature, inventory_of

TRUE = Atom("$true", ())
FALSE = Atom("$false", ())
TOP = Atom("⊤", ())
BOT = Atom("⊥", ())
P = Atom("P", ())
Q = Atom("Q", ())

CONSTANTS = [TRUE, FALSE, TOP, BOT]
CONSTANT_IDS = ["$true", "$false", "top-glyph", "bot-glyph"]


# ---------------------------------------------------------------------------
# The signature
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("constant", CONSTANTS, ids=CONSTANT_IDS)
def test_a_signature_does_not_call_a_truth_constant_undeclared(constant):
    signature = Signature.from_dict({"predicates": {"P": {"arity": 0}}})
    assert signature.validate(constant) == []
    assert signature.validate(Implies(And(P, constant), Not(constant))) == []


@pytest.mark.parametrize("constant", CONSTANTS, ids=CONSTANT_IDS)
def test_a_signature_still_reports_the_undeclared_predicates_beside_a_constant(constant):
    signature = Signature.from_dict({"predicates": {"P": {"arity": 0}}})
    assert signature.validate(And(Q, constant)) == ["undeclared predicate 'Q' (arity 0)"]


@pytest.mark.parametrize("constant", CONSTANTS, ids=CONSTANT_IDS)
def test_a_signature_inferred_from_formulas_lists_no_predicate_for_a_constant(constant):
    assert dict(Signature.from_formulas([constant]).predicates) == {}
    inferred = Signature.from_formulas([Implies(And(P, constant), Not(constant))])
    assert sorted(inferred.predicates) == ["P"]


@pytest.mark.parametrize("constant", CONSTANTS, ids=CONSTANT_IDS)
def test_the_symbol_inventory_lists_no_predicate_for_a_constant(constant):
    predicates, functions, constants = inventory_of(Implies(And(P, constant), Not(constant)))
    assert predicates == {("P", 0)}
    assert functions == set() and constants == set()


@pytest.mark.parametrize("name", ["$true", "$false", "⊤", "⊥"])
def test_the_same_name_with_arguments_is_an_ordinary_undeclared_predicate(name):
    odd = Atom(name, [Constant("a")])
    signature = Signature.from_dict({"predicates": {"P": {"arity": 0}}})
    assert f"undeclared predicate '{name}' (arity 1)" in signature.validate(odd)
    assert ((name, 1)) in inventory_of(odd)[0]
    assert name in Signature.from_formulas([odd]).predicates


# ---------------------------------------------------------------------------
# The Prover9 reader
# ---------------------------------------------------------------------------

def test_the_prover9_reader_reads_dollar_t_and_dollar_f_as_the_constants():
    from unicode_fol_kit.fol.prover9_input import parse_prover9
    assert parse_prover9("$T") == TRUE
    assert parse_prover9("$F") == FALSE
    assert parse_prover9("$T.") == TRUE                      # a trailing period ends the formula
    assert parse_prover9("-($F)") == Not(FALSE)
    assert parse_prover9("$T -> P") == Implies(TRUE, P)
    assert parse_prover9("($F | P) & $T") == And(Or(FALSE, P), TRUE)
    assert parse_prover9("q <-> $F") == Iff(Atom("q", ()), FALSE)


@pytest.mark.parametrize("node", [TRUE, FALSE, Not(FALSE), Implies(And(P, TRUE), Not(FALSE)),
                                  Or(FALSE, Quantifier("∀", Variable("x"), Atom("R", [Variable("x")])))])
def test_what_the_prover9_writer_writes_for_the_constants_reads_back(node):
    from unicode_fol_kit.fol.prover9_input import parse_prover9
    assert parse_prover9(node.to_prover9()) == node


def test_the_glyph_atoms_are_written_as_the_constants_and_read_back_as_them():
    from unicode_fol_kit.fol.prover9_input import parse_prover9
    assert parse_prover9(TOP.to_prover9()) == TRUE
    assert parse_prover9(BOT.to_prover9()) == FALSE


def test_a_prover9_problem_with_the_constants_reads_back():
    from unicode_fol_kit.atp.prover9_entailment import generate_prover9_input_with_mapping
    from unicode_fol_kit.fol.prover9_input import parse_prover9_problem
    text = generate_prover9_input_with_mapping([FALSE, Implies(Q, TRUE)], Q)[0]
    read = [(item.role, item.formula) for item in parse_prover9_problem(text)]
    assert read == [("assumptions", FALSE), ("assumptions", Implies(Atom("q", ()), TRUE)),
                    ("goals", Atom("q", ()))]


@pytest.mark.parametrize("text", ["$Tx", "$T1", "P($T)", "$T = $T", "$t", "$X", "f($F) = a"])
def test_a_dollar_word_that_is_not_one_of_the_two_constants_is_refused(text):
    from unicode_fol_kit.fol.prover9_input import Prover9ParsingError, parse_prover9
    with pytest.raises(Prover9ParsingError):
        parse_prover9(text)


# ---------------------------------------------------------------------------
# The CASL reader
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("formulas", [
    [TRUE], [FALSE], [Implies(And(P, TRUE), Not(FALSE))],
    [Quantifier("∀", Variable("x"), And(TRUE, Atom("R", [Variable("x")])))],
], ids=["true", "false", "connectives", "under-a-quantifier"])
def test_a_casl_spec_the_exporter_writes_for_the_constants_reads_back(formulas):
    from unicode_fol_kit.fol.casl_export import to_casl_spec
    from unicode_fol_kit.fol.casl_import import parse_casl_spec
    spec = parse_casl_spec(to_casl_spec(formulas))
    assert list(spec.axioms) == formulas
    # the constants declare no predicate: only the vocabulary the formulas really use is declared
    assert "$true" not in spec.signature.predicates and "$false" not in spec.signature.predicates
    assert sorted(spec.signature.predicates) == sorted(
        {n.predicate for f in formulas for n in f.walk()
         if isinstance(n, Atom) and n.predicate not in ("$true", "$false")})


def test_a_casl_text_written_by_hand_reads_true_and_false_as_the_constants():
    from unicode_fol_kit.fol.casl_import import parse_casl_spec
    text = "spec S =\n  preds P : ()\n  . true => P\n  . not false %implied\nend"
    spec = parse_casl_spec(text)
    assert spec.axioms == (Implies(TRUE, P),)
    assert spec.conjectures == (Not(FALSE),)


@pytest.mark.parametrize("text, reason", [
    ("spec S =\n  preds true : ()\n  . true\nend", "predicate name 'true' collides"),
    ("spec S =\n  sorts false\nend", "sort name 'false' collides"),
    ("spec S =\n  preds P : ()\n  . P(true)\nend", "name 'true' collides"),
    ("spec S =\n  preds P : ()\n  . true(a)\nend", "'true' is a CASL formula"),
    ("spec S =\n  preds P : ()\n  . false = a\nend", "'false' is a CASL formula"),
    ("spec S =\n  preds P : ()\n  . P => trueish\nend", "predicate 'trueish' is used but never declared"),
])
def test_true_and_false_stay_refused_as_names_and_are_no_terms(text, reason):
    from unicode_fol_kit.fol.casl_import import CaslImportError, parse_casl_spec
    with pytest.raises(CaslImportError) as caught:
        parse_casl_spec(text)
    assert reason in str(caught.value)


# ---------------------------------------------------------------------------
# The repair of a formula
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("text, expected, rendered", [
    ("P -> ⊥", Implies(P, FALSE), "P → ⊥"),
    ("P -> ⊤", Implies(P, TRUE), "P → ⊤"),
    ("⊥ -> P", Implies(FALSE, P), "⊥ → P"),
    ("P <-> ⊥", Iff(P, FALSE), "P ↔ ⊥"),
    ("~⊥", Not(FALSE), "¬⊥"),
    ("P -> Q -> ⊥", Implies(P, Implies(Q, FALSE)), "P → Q → ⊥"),    # the arrow is right-associative
])
def test_a_truth_glyph_beside_an_ascii_arrow_is_repaired_like_the_arrow_alone(text, expected, rendered):
    from unicode_fol_kit.fol.dialect_repair import repair_formula
    result = repair_formula(text)
    assert result.ok and result.changed
    assert result.repaired_text == rendered
    assert result.formula == expected
    assert [issue.kind for issue in result.issues] == ["truth_glyph"]
    # the repaired text reads back to the repaired formula
    from unicode_fol_kit import api
    assert api.parse_any(result.repaired_text).formula == result.formula


def test_the_repair_of_a_glyph_beside_an_arrow_matches_the_repair_of_a_letter_there():
    from unicode_fol_kit.fol.dialect_repair import repair_formula
    letter = repair_formula("P -> Q")
    glyph = repair_formula("P -> ⊥")
    assert (letter.ok, letter.changed, letter.dialect) == (glyph.ok, glyph.changed, glyph.dialect)
    assert letter.repaired_text == "P → Q"


def test_a_text_that_parses_is_not_touched_by_the_glyph_repair():
    from unicode_fol_kit.fol.dialect_repair import repair_formula
    for text in ("P → ⊥", "¬⊥", "⊥", "P ∧ ⊤"):
        result = repair_formula(text)
        assert result.ok and not result.changed and result.issues == (), text


def test_the_glyph_repair_does_not_hide_a_mixed_connective_refusal_or_another_error():
    from unicode_fol_kit.fol.dialect_repair import repair_formula
    mixed = repair_formula("P ∧ Q ∨ ⊥")
    assert not mixed.ok and [i.kind for i in mixed.issues] == ["mixed_connectives"]
    # a glyph is not the only obstacle: the text does not parse with the glyph spelled as a constant either
    for text in ("P and ⊥", "P -> ⊥ ⊤"):
        result = repair_formula(text)
        assert not result.ok and result.repaired_text == text
        assert [i.kind for i in result.issues] == ["syntax_error"]


def test_a_pinned_dialect_is_respected_by_the_glyph_repair():
    from unicode_fol_kit.fol.dialect_repair import repair_formula
    # the unicode ladder does not read `->`, and a pinned dialect is not left for another
    assert not repair_formula("P -> ⊥", dialect="unicode").ok
    pinned = repair_formula("P -> ⊥", dialect="prover9")
    assert pinned.ok and pinned.dialect == "prover9" and pinned.formula == Implies(P, FALSE)


# ---------------------------------------------------------------------------
# The verbalisers
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("formula, sentence", [
    (TRUE, "truth"),
    (FALSE, "falsity"),
    (TOP, "truth"),
    (BOT, "falsity"),
    (Not(FALSE), "it is not the case that falsity"),
    (Not(BOT), "it is not the case that falsity"),
    (Not(TRUE), "it is not the case that truth"),
    (Implies(P, FALSE), "if P, then falsity"),
    (Implies(BOT, P), "if falsity, then P"),
    (And(TRUE, P), "truth and P"),
    (Or(FALSE, P), "falsity or P"),
    (Quantifier("∀", Variable("x"), Implies(Atom("Human", [Variable("x")]), BOT)),
     "for every x, if x is human, then falsity"),
])
def test_the_english_verbaliser_says_truth_and_falsity(formula, sentence):
    from unicode_fol_kit.fol import to_english
    assert to_english(formula) == sentence


def test_a_proposition_that_is_no_constant_is_still_read_as_its_name():
    from unicode_fol_kit.fol import to_english
    assert to_english(Atom("Rain", ())) == "Rain"
    assert to_english(Not(Atom("Rain", ()))) == "it is not the case that Rain"
    # the reserved words with an argument are predicates like any other
    assert to_english(Atom("$true", [Constant("a")])) == "a is $true"
    assert to_english(Atom("⊥", [Constant("a")])) == "a is ⊥"


@pytest.mark.parametrize("constant", CONSTANTS, ids=CONSTANT_IDS)
def test_the_ace_verbaliser_refuses_a_truth_constant_by_name(constant):
    from unicode_fol_kit.ace.verbalize import formula_to_ace, modal_formula_to_ace
    from unicode_fol_kit.drt.reverse import FolToDrsError
    man = Atom("Man", [Constant("john")])
    for formula in (constant, Not(constant), And(man, constant)):
        with pytest.raises(FolToDrsError) as caught:
            formula_to_ace(formula)
        message = str(caught.value)
        assert f"the truth constant {constant.predicate} has no ACE sentence" in message
        assert "formula_to_ace" in message and "to_english" in message
    with pytest.raises(FolToDrsError) as caught:
        modal_formula_to_ace(Box(constant))
    assert "modal_formula_to_ace" in str(caught.value)
    assert f"the truth constant {constant.predicate}" in str(caught.value)


def test_the_ace_verbaliser_is_unchanged_for_a_formula_without_a_constant():
    from unicode_fol_kit.ace.verbalize import formula_to_ace
    from unicode_fol_kit.drt.reverse import FolToDrsError
    with pytest.raises(FolToDrsError) as caught:
        formula_to_ace(Atom("P", ()))                  # a bare proposition: its own refusal
    assert "truth constant" not in str(caught.value)
