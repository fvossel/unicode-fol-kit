"""Tests for :mod:`unicode_fol_kit.fol.prolog_input`.

Every expected AST is hand-derived from the clause, never copied from a run.
Two conventions drive all of them and are worth stating once:

* Prolog spells a predicate lower-case and a variable upper-case; the kit does
  the exact opposite, so ``carbon(A)`` must come back as ``Carbon(a)`` — the
  same inversion :mod:`unicode_fol_kit.fol.tptp_input` applies.
* Only the FIRST character is folded. ``bSINGLE`` is already a legal Prolog
  atom, so it must arrive as ``BSINGLE`` and not as ``Bsingle``; lower-casing
  the whole name would destroy a distinction ChemLog's vocabulary makes.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Implies, Not, Number, Or, Quantifier,
    Variable,
)
from unicode_fol_kit.fol.prolog_input import (
    PrologParsingError, load_prolog, parse_prolog_clause, parse_prolog_program,
)


# ---------------------------------------------------------------------------
# The two readings
# ---------------------------------------------------------------------------

def test_clause_mode_is_the_standard_universally_closed_implication():
    """``h(A) :- b(A, B).`` is ∀a∀b (B(a,b) → H(a)).

    Hand-derived: body implies head (not the other way round — the arrow in
    ``:-`` points left), every variable universally quantified over the whole
    clause, in alphabetical order outermost-first.
    """
    a, b = Variable("a"), Variable("b")
    expected = Quantifier("∀", a, Quantifier("∀", b, Implies(
        Atom("B", [a, b]), Atom("H", [a]))))

    assert parse_prolog_clause("h(A) :- b(A, B).") == expected


def test_body_mode_keeps_the_head_variables_free_and_closes_the_rest():
    """The same clause read as a DEFINITION: only the condition, with ``B``
    (body-only) existentially closed and ``A`` (the head's) left free, ready
    to be model-checked against one structure."""
    a, b = Variable("a"), Variable("b")
    expected = Quantifier("∃", b, Atom("B", [a, b]))

    assert parse_prolog_clause("h(A) :- b(A, B).", mode="body") == expected


def test_the_two_readings_are_genuinely_different_formulas():
    """Not a formatting difference: one is an implication about everything,
    the other a condition with a free variable. The module refuses to pick."""
    text = "h(A) :- b(A, B)."
    assert (parse_prolog_clause(text, mode="clause")
            != parse_prolog_clause(text, mode="body"))


def test_a_fact_is_its_head_closed_in_clause_mode_and_bare_in_body_mode():
    """A fact has no condition, so body mode returns the head itself rather
    than inventing a ⊤ the caller never wrote."""
    assert parse_prolog_clause("carbon(a).") == Atom("Carbon", [Constant("a")])
    assert (parse_prolog_clause("p(X).")
            == Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])))
    assert (parse_prolog_clause("p(X).", mode="body")
            == Atom("P", [Variable("x")]))


# ---------------------------------------------------------------------------
# Naming
# ---------------------------------------------------------------------------

def test_only_the_first_character_is_folded_in_either_direction():
    """``bSINGLE`` is a legal Prolog atom and must survive as ``BSINGLE``.
    Lower-casing the whole name would collapse ChemLog's ``bSINGLE`` and a
    hypothetical ``bsingle`` into one predicate."""
    node = parse_prolog_clause("amide(A) :- bSINGLE(A, B).", mode="body")

    assert node == Quantifier("∃", Variable("b"),
                              Atom("BSINGLE", [Variable("a"), Variable("b")]))


def test_a_quoted_atom_keeps_its_exact_characters():
    """A name that is not a legal bare atom arrives verbatim — the caller
    runs ``sanitize_names`` if it needs to be rendered back to kit text."""
    node = parse_prolog_clause("cls(A) :- '1,2-diacyl'(A).", mode="body")

    assert node == Atom("1,2-diacyl", [Variable("a")])


def test_each_anonymous_variable_is_a_distinct_fresh_one():
    """``_`` twice means two independent positions; collapsing them would
    equate arguments Prolog keeps apart."""
    node = parse_prolog_clause("p(A) :- q(A, _), r(A, _).", mode="body")

    variables = [part.name for part in node.walk()
                 if isinstance(part, Variable) and part.name.startswith("_")]
    assert len(set(variables)) == 2


# ---------------------------------------------------------------------------
# Body structure
# ---------------------------------------------------------------------------

def test_comma_is_conjunction_and_semicolon_is_disjunction():
    a = Variable("a")
    assert (parse_prolog_clause("p(A) :- q(A), r(A).", mode="body")
            == And(Atom("Q", [a]), Atom("R", [a])))
    assert (parse_prolog_clause("p(A) :- q(A) ; r(A).", mode="body")
            == Or(Atom("Q", [a]), Atom("R", [a])))


def test_comma_binds_tighter_than_semicolon():
    """Prolog's own precedence: ``q, r ; s`` is ``(q ∧ r) ∨ s``."""
    a = Variable("a")
    assert (parse_prolog_clause("p(A) :- q(A), r(A) ; s(A).", mode="body")
            == Or(And(Atom("Q", [a]), Atom("R", [a])), Atom("S", [a])))


def test_a_compound_term_becomes_a_function_not_a_predicate():
    """Inside an argument list, ``f(a)`` is a TERM. Reading it as a predicate
    would put a formula where an individual belongs."""
    node = parse_prolog_clause("p(A) :- q(f(a), 3).", mode="body")

    assert node == Atom("Q", [Function("f", [Constant("a")]), Number(3)])


# ---------------------------------------------------------------------------
# What it refuses, and why
# ---------------------------------------------------------------------------

def test_negation_as_failure_is_refused_by_default():
    """``\\+`` means 'not derivable', which is ``¬`` only under the closed
    world assumption. Reading it silently would turn "not derivable here"
    into "false everywhere"."""
    with pytest.raises(PrologParsingError, match="closed world assumption"):
        parse_prolog_clause("p(A) :- q(A), \\+ r(A).", mode="body")


def test_negation_as_failure_becomes_classical_negation_on_opt_in():
    a = Variable("a")
    node = parse_prolog_clause("p(A) :- q(A), \\+ r(A).", mode="body",
                               negation_as_failure="classical")

    assert node == And(Atom("Q", [a]), Not(Atom("R", [a])))


@pytest.mark.parametrize("text, needle", [
    ("p(A) :- q(A), !.", "cut"),
    ("p(A) :- q(A) -> r(A).", "if-then"),
    ("p(A) :- foo is 1.", "arithmetic"),
    ("p(A) :- q =.. L.", "univ"),
    ("p(A) :- q([1, 2]).", "list syntax"),
])
def test_constructs_with_no_first_order_reading_are_refused_by_name(text, needle):
    """Each of these would change what the clause means if dropped, so the
    refusal names the construct instead of reporting a generic syntax error
    that sends the reader looking for a typo."""
    with pytest.raises(PrologParsingError, match=needle):
        parse_prolog_clause(text, mode="body")


def test_two_clauses_in_one_call_are_refused_with_the_right_advice():
    with pytest.raises(PrologParsingError, match="parse_prolog_program"):
        parse_prolog_clause("p(A). q(A).")


def test_an_unknown_mode_is_refused_before_anything_is_parsed():
    with pytest.raises(PrologParsingError, match="unknown mode"):
        parse_prolog_clause("p(a).", mode="nonsense")


# ---------------------------------------------------------------------------
# Programs
# ---------------------------------------------------------------------------

def test_a_program_splits_on_clause_ending_periods_only():
    """Not on a decimal point, not on a period inside a quoted atom, and
    comments are skipped."""
    program = """
    % a comment with a period.
    val(1.5).
    name('a.b').
    p(A) :- q(A).
    """
    clauses = parse_prolog_program(program)

    assert len(clauses) == 3
    assert clauses[0] == Atom("Val", [Number(1.5)])
    assert clauses[1] == Atom("Name", [Constant("a.b")])


def test_alternative_clauses_are_returned_separately_not_disjoined():
    """Two clauses with one head ARE alternatives, but only under the
    completion of the program — an assumption about the whole program, not a
    fact about these two clauses. Asserting it here would strengthen what the
    caller wrote."""
    clauses = parse_prolog_program("p(A) :- q(A).\np(A) :- r(A).")

    assert len(clauses) == 2
    assert all(isinstance(clause, Quantifier) for clause in clauses)
    assert not any(isinstance(part, Or)
                   for clause in clauses for part in clause.walk())


def test_a_failing_clause_names_itself_in_the_message():
    with pytest.raises(PrologParsingError, match="in clause:"):
        parse_prolog_program("p(a).\nq(A) :- r(A), !.")


def test_load_prolog_reads_a_file(tmp_path):
    path = tmp_path / "program.pl"
    path.write_text("p(a).\nq(b).\n", encoding="utf-8")

    assert load_prolog(str(path)) == [Atom("P", [Constant("a")]),
                                      Atom("Q", [Constant("b")])]


# ---------------------------------------------------------------------------
# The end-to-end reason this module exists
# ---------------------------------------------------------------------------

def test_a_learned_clause_can_be_checked_against_a_molecule():
    """The round trip an ILP result has to survive: clause -> AST -> model
    check, with no hand-written translation in between.

    The clause is a real Popper output for "has an amide bond", in the
    encoding where ``atom_in/2`` alone carries the example. Hand-derived
    verdicts: glycylglycine's peptide bond is an N single-bonded to a carbon
    that is double-bonded to an O, so it holds; ethanol has no nitrogen at
    all, so it cannot.
    """
    rdkit = pytest.importorskip("rdkit")           # noqa: F841
    from unicode_fol_kit import chem
    from unicode_fol_kit.semantics.model_eval import evaluate_detailed

    node = parse_prolog_clause(
        "amide(A) :- bSINGLE(C, D), bDOUBLE(D, B), n(C), atom_in(A, B).",
        mode="body")
    # Drop the membership literal: it anchors the clause to its example and
    # says nothing about the structure being checked.
    def strip(part):
        if isinstance(part, Quantifier):
            inner = strip(part.formula)
            return (Quantifier(part.type, part.variable, inner)
                    if inner is not None else None)
        if isinstance(part, And):
            left, right = strip(part.left), strip(part.right)
            return left if right is None else (right if left is None
                                               else And(left, right))
        return None if (isinstance(part, Atom)
                        and part.predicate == "Atom_in") else part

    body = chem.to_chemlog_names(strip(node))
    holds = {smiles: evaluate_detailed(
                body, chem.mol_to_structure(smiles, computed=False),
                all_different=True).holds
             for smiles in ("NCC(=O)NCC(=O)O", "CCO")}

    assert holds["NCC(=O)NCC(=O)O"] is True
    assert holds["CCO"] is False
