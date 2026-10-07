"""Tests for the TF0 (monomorphic typed TPTP ``tff``) half of ``fol/tptp_input.py``.

The classical ``fof``/``cnf`` reading in this module already has its own
regression coverage (``test_tptp_header.py``, ``test_tptp_problem.py``,
``test_tptp_ncl.py``, ``test_tptp_repair.py``); this file is purely additive
and covers only what C2 (native TF0 reader/writer) added:

* ``parse_tptp``/``parse_tptp_formula``/``load_tptp`` now also accept ``tff``
  AXIOM/CONJECTURE statements (typed quantifiers), and reject a ``tff``
  TYPE DECLARATION with a message pointing at :func:`parse_tff_problem`.
* :func:`parse_tff_problem` — the typed reader: declared
  :class:`~unicode_logic_kit.fol.signature.Signature` + formulas, with a bare
  ``Constant`` occurrence promoted to ``SortedConstant`` wherever its name
  was declared with a concrete sort.
* The three explicit TF0-scope refusals: THF, TF1 polymorphism (``!>``), and
  the arithmetic sorts ``$int``/``$rat``/``$real`` — each a NAMED,
  ``NotImplementedError``/``ParsingError`` refusal, never a silent parse.

No snapshot tests: every expected AST below is either built directly with
the kit's own node constructors, or (per this module's own test_oracle)
cross-checked against ``MSFLParser(many_sorted=True)`` parsing the
equivalent Unicode text — an INDEPENDENT second route, not
``parse_tff_problem``'s own output copied back in.
"""

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.fol.naming import ParsingError
from unicode_logic_kit.fol.nodes import (
    Atom, Constant, SortedConstant, SortedQuantifier, Quantifier, Variable,
    Implies, Function,
)
from unicode_logic_kit.fol.signature import Signature, PredicateDecl, FunctionDecl, ConstantDecl
from unicode_logic_kit.fol.tptp_input import (
    parse_tptp, parse_tptp_formula, load_tptp, TptpFormula,
    parse_tff_problem, load_tff_problem,
)

MSFOL = MSFLParser(many_sorted=True)


# =============================================================================
# parse_tptp / parse_tptp_formula: tff AXIOM/CONJECTURE statements now read
# =============================================================================

def test_parse_tptp_accepts_tff_axiom_with_typed_quantifier():
    """A tff(...) formula statement is read exactly like fof(...), except a
    typed quantifier builds a SortedQuantifier instead of a plain one."""
    [rec] = parse_tptp("tff(ax, axiom, ![X: human] : (p(X) => q(X)) ).")
    assert rec == TptpFormula(
        "ax", "axiom",
        SortedQuantifier("∀", Variable("x"), "Human",
                         Implies(Atom("P", [Variable("x")]), Atom("Q", [Variable("x")]))),
    )


def test_parse_tptp_formula_untyped_quantifier_unchanged():
    """An untyped tff/fof quantifier still builds a plain Quantifier -- the
    grammar widening is additive, not a behaviour change for existing fof text."""
    node = parse_tptp_formula("![X]: (p(X) => q(X))")
    assert node == Quantifier(
        "∀", Variable("x"),
        Implies(Atom("P", [Variable("x")]), Atom("Q", [Variable("x")])))
    assert not isinstance(node, SortedQuantifier)


def test_parse_tptp_formula_explicit_i_type_is_untyped():
    """"$i" (the default individual type) resolves to a PLAIN Quantifier,
    not a SortedQuantifier -- "typed as $i" and "untyped" are the same
    thing to the kit's own AST (there is no first-class "$i" sort name)."""
    node = parse_tptp_formula("![X: $i]: p(X)")
    assert node == Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    assert not isinstance(node, SortedQuantifier)


def test_parse_tptp_multi_variable_typed_list():
    """"! [X: human, Y: dog] : ..." binds both variables, each to its own sort."""
    node = parse_tptp_formula("![X: human, Y: dog]: owns(X,Y)")
    assert node == SortedQuantifier(
        "∀", Variable("x"), "Human",
        SortedQuantifier("∀", Variable("y"), "Dog", Atom("Owns", [Variable("x"), Variable("y")])))


def test_parse_tptp_rejects_type_declaration():
    """parse_tptp cannot represent a type declaration as a TptpFormula --
    it must redirect the caller to parse_tff_problem, not drop it silently."""
    text = "tff(s_type, type, human: $tType ). tff(ax, axiom, p )."
    with pytest.raises(ParsingError, match="parse_tff_problem"):
        parse_tptp(text)


def test_parse_tptp_thf_refused_by_name():
    with pytest.raises(ParsingError, match="THF"):
        parse_tptp("thf(a, axiom, p).")


# =============================================================================
# parse_tff_problem: round-trip golden cases
# =============================================================================
#
# Each golden case's EXPECTED AST is built two independent ways: (1) directly
# via MSFLParser(many_sorted=True).parse(<unicode text>) -- reasoning through
# what tree that produces from the grammar, same as test_casl_import.py's own
# convention -- and (2) never by running parse_tff_problem and copying its
# output back in.

def test_round_trip_socrates_syllogism():
    """The textbook syllogism, hand-written as real TF0 TPTP text (product-
    free unary predicates/sorts -- the simplest possible shape)."""
    text = """
    tff(human_type, type, human: $tType ).
    tff(mortal_decl, type, mortal: human > $o ).
    tff(human_decl, type, human_p: human > $o ).
    tff(socrates_decl, type, socrates: human ).

    tff(ax1, axiom, ![X: human] : (human_p(X) => mortal(X)) ).
    tff(ax2, axiom, human_p(socrates) ).
    tff(goal, conjecture, mortal(socrates) ).
    """
    sig, formulas = parse_tff_problem(text)

    expected_sig = Signature(
        predicates={
            "Human_p": PredicateDecl("Human_p", 1, ("Human",)),
            "Mortal": PredicateDecl("Mortal", 1, ("Human",)),
        },
        constants={"socrates": ConstantDecl("socrates", "Human")},
        sorts=frozenset({"Human"}),
    )
    assert sig == expected_sig

    # Independent second route: build the same three formulas by hand via
    # MSFLParser(many_sorted=True) parsing the kit's OWN Unicode syntax.
    expected_formulas = [
        MSFOL.parse("∀x:Human (Human_p(x) → Mortal(x))"),
        MSFOL.parse("Human_p(socrates:Human)"),
        MSFOL.parse("Mortal(socrates:Human)"),
    ]
    assert [f.formula for f in formulas] == expected_formulas
    assert [f.role for f in formulas] == ["axiom", "axiom", "conjecture"]


def test_round_trip_two_sort_disjoint_domain():
    """Two sorts that never mix (Human/Dog), each with its own predicate and
    constant -- a "peaceful multi-sort coexistence" golden case."""
    text = """
    tff(human_type, type, human: $tType ).
    tff(dog_type, type, dog: $tType ).
    tff(mortal_decl, type, mortal: human > $o ).
    tff(barks_decl, type, barks: dog > $o ).
    tff(alice_decl, type, alice: human ).
    tff(rex_decl, type, rex: dog ).

    tff(ax1, axiom, mortal(alice) ).
    tff(ax2, axiom, barks(rex) ).
    """
    sig, formulas = parse_tff_problem(text)
    assert sig.sorts == frozenset({"Human", "Dog"})
    assert sig.predicates == {
        "Mortal": PredicateDecl("Mortal", 1, ("Human",)),
        "Barks": PredicateDecl("Barks", 1, ("Dog",)),
    }
    assert sig.constants == {
        "alice": ConstantDecl("alice", "Human"),
        "rex": ConstantDecl("rex", "Dog"),
    }
    assert [f.formula for f in formulas] == [
        MSFOL.parse("Mortal(alice:Human)"),
        MSFOL.parse("Barks(rex:Dog)"),
    ]


def test_round_trip_sorted_function():
    """A sorted function symbol (fatherOf: human > human) round-trips into
    Function applications, with the function's own sort info living only in
    the returned Signature (Function carries no sort field -- see module
    docstring)."""
    text = """
    tff(human_type, type, human: $tType ).
    tff(father_of_decl, type, father_of: human > human ).
    tff(mortal_decl, type, mortal: human > $o ).
    tff(alice_decl, type, alice: human ).

    tff(ax1, axiom, ![X: human] : mortal(father_of(X)) ).
    tff(goal, conjecture, mortal(father_of(alice)) ).
    """
    sig, formulas = parse_tff_problem(text)
    assert sig.functions == {
        "father_of": FunctionDecl("father_of", 1, ("Human",), "Human"),
    }
    expected = [
        MSFOL.parse("∀x:Human Mortal(father_of(x))"),
        MSFOL.parse("Mortal(father_of(alice:Human))"),
    ]
    assert [f.formula for f in formulas] == expected


def test_round_trip_binary_predicate_product_domain():
    """A 2-ary predicate's declaration needs TFF's parenthesised product
    domain ("(human * dog) > $o") -- the real-file BNF shape, not the
    single-argument "S > $o" shortcut the other golden cases use."""
    text = """
    tff(human_type, type, human: $tType ).
    tff(dog_type, type, dog: $tType ).
    tff(owns_decl, type, owns: ( human * dog ) > $o ).
    tff(alice_decl, type, alice: human ).
    tff(rex_decl, type, rex: dog ).

    tff(ax, axiom, owns(alice, rex) ).
    """
    sig, formulas = parse_tff_problem(text)
    assert sig.predicates == {"Owns": PredicateDecl("Owns", 2, ("Human", "Dog"))}
    assert formulas[0].formula == MSFOL.parse("Owns(alice:Human, rex:Dog)")


def test_constant_promoted_to_sorted_constant_from_declaration():
    """A bare 'socrates' occurrence in a formula BODY carries no inline sort
    (only a bound variable does) -- the promotion from plain Constant to
    SortedConstant must come from the SEPARATE type declaration."""
    text = """
    tff(human_type, type, human: $tType ).
    tff(socrates_decl, type, socrates: human ).
    tff(mortal_decl, type, mortal: human > $o ).
    tff(ax, axiom, mortal(socrates) ).
    """
    _sig, [rec] = parse_tff_problem(text)
    [arg] = rec.formula.args
    assert arg == SortedConstant("socrates", "Human")


def test_unsorted_constant_stays_a_plain_constant():
    """A constant declared (or used) with type $i is never promoted -- it
    stays a plain Constant, matching a formula that never mentions sorts."""
    text = """
    tff(c_decl, type, c: $i ).
    tff(p_decl, type, p: $i > $o ).
    tff(ax, axiom, p(c) ).
    """
    sig, [rec] = parse_tff_problem(text)
    assert sig.constants["c"].sort is None
    [arg] = rec.formula.args
    assert arg == Constant("c")
    assert not isinstance(arg, SortedConstant)


def test_load_tff_problem_reads_a_file(tmp_path):
    path = tmp_path / "problem.p"
    path.write_text(
        "tff(human_type, type, human: $tType ).\n"
        "tff(mortal_decl, type, mortal: human > $o ).\n"
        "tff(alice_decl, type, alice: human ).\n"
        "tff(ax, axiom, mortal(alice) ).\n",
        encoding="utf-8",
    )
    sig, [rec] = load_tff_problem(str(path))
    assert sig.sorts == frozenset({"Human"})
    assert rec.formula == MSFOL.parse("Mortal(alice:Human)")


# =============================================================================
# Refusals: THF / TF1 polymorphism / arithmetic sorts, each named
# =============================================================================

def test_thf_statement_refused_before_tff_grammar_even_engages():
    with pytest.raises(ParsingError, match="THF"):
        parse_tff_problem("thf(a, type, p: $o ).")


def test_tf1_polymorphism_refused_by_name():
    """"!> [A] : (A > A)" is TF1 (polymorphic) syntax -- NotImplementedError,
    naming TF1 polymorphism specifically, not a generic parse failure."""
    with pytest.raises(NotImplementedError, match="[Pp]olymorphic"):
        parse_tff_problem("tff(f_type, type, f: !>[A]: (A > A) ).")


@pytest.mark.parametrize("sort", ["$int", "$rat", "$real"])
def test_arithmetic_sort_declaration_refused_by_name(sort):
    with pytest.raises(NotImplementedError, match="arithmetic"):
        parse_tff_problem(f"tff(n_type, type, n: {sort} ).")


@pytest.mark.parametrize("sort", ["$int", "$rat", "$real"])
def test_arithmetic_sort_as_quantifier_type_refused_by_name(sort):
    with pytest.raises(NotImplementedError, match="arithmetic"):
        parse_tff_problem(f"tff(ax, axiom, ![X: {sort}] : p(X) ).")


def test_boolean_type_as_quantifier_variable_refused():
    """"$o" is only ever a predicate's own overall result -- never a
    quantified variable's type."""
    with pytest.raises(ParsingError, match=r"\$o"):
        parse_tff_problem("tff(ax, axiom, ![X: $o] : p(X) ).")


def test_conflicting_duplicate_declaration_refused():
    """The same predicate declared twice with two DIFFERENT types is a
    malformed problem -- refused, not silently overwritten."""
    text = """
    tff(human_type, type, human: $tType ).
    tff(dog_type, type, dog: $tType ).
    tff(p_decl_1, type, p: human > $o ).
    tff(p_decl_2, type, p: dog > $o ).
    tff(ax, axiom, p(a) ).
    """
    with pytest.raises(ParsingError, match="'P'"):
        parse_tff_problem(text)
