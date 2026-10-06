"""Tests for the public SMT-LIB2 writer (``atp.z3_input.to_smtlib`` /
``Node.to_smtlib``).

Oracles, hand-checked, each justified inline:

* **round trip**: ``z3.parse_smt2_string(to_smtlib(formula, premises))`` fed
  back through the kit's own :func:`~unicode_fol_kit.atp.z3_input.from_z3`
  reproduces the input up to the documented, already-tested lossiness table
  in ``z3_input.py``'s own module docstring (free :class:`Variable`/
  :class:`Constant`/:class:`Number` collapse onto one uninterpreted sort;
  bound :class:`Variable`\\ s are preserved) — checked structurally, against the
  formula the name map of the sanitiser says the text holds;
* **differential against Z3 itself**: the SAME entailment question, asked
  once directly via ``Node.to_z3()`` into a fresh ``z3.Solver`` and once by
  reparsing ``to_smtlib``'s own output text, must get the SAME sat/unsat
  verdict — this is what actually exercises the SMT-LIB2 *text* round trip,
  as opposed to just the AST-level one;
* **legality against Z3's own parser**: three adversarial name shapes
  (digit-leading ASCII, an SMT-LIB2 reserved word, non-ASCII) are checked
  both positively (the exported text parses) and, for the two this module's
  sanitiser actually has to fix, negatively (the SAME name run through the
  naive ``to_z3()`` + ``z3.Solver.to_smt2()`` combination — no sanitiser —
  fails to parse; this is the regression the sanitiser exists to prevent,
  and a passing positive test alone would not distinguish "fixed" from
  "was never broken");
* **cvc5, where installed**: the exported text is also legal cvc5 input and
  cvc5 agrees with Z3 on a ground (quantifier-free, hence fully decidable by
  both — no risk of cvc5's own instantiation search coming back "unknown")
  satisfiability question;
* **refusal**: a construct ``Node.to_z3`` itself refuses (second-order
  quantification, a modal operator) must refuse through ``to_smtlib`` too,
  with the SAME message plus one sentence naming this entry point — never
  silently dropped or mistranslated.

Reserved-word names (``let``, ...) are a gap this task found live in
:mod:`unicode_fol_kit.atp.cvc5_backend`'s existing sanitiser (which
previously caught only digit-leading names) and fixed there, since
``to_smtlib`` reuses that same sanitiser rather than duplicating it — see
that module's docstring and ``_SMTLIB_RESERVED_WORDS``.
"""

import pytest
import z3

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Atom, Constant, Function, Number, Variable,
)
from unicode_fol_kit.atp.z3_input import to_smtlib, parse_smtlib
from unicode_fol_kit.atp.cvc5_backend import _sanitize_many_for_smtlib

_P = MSFLParser()


# ---------------------------------------------------------------------------
# Round trip: propositional, quantified + equality, "arithmetic"-flavoured
# (Number/+/-/*// are uninterpreted-sort symbols under the plain to_z3()
# route this writer uses — see fol/_fol_nodes.py's Function/Number.to_z3 —
# not genuine Z3 Int/Real; atp.z3_arith is the separate module for that).
# ---------------------------------------------------------------------------

def test_propositional_round_trip():
    # P(alice) ∧ ¬Q(alice): no quantifiers and every argument is already a
    # multi-letter Constant (a single lowercase letter such as "a" lexes as
    # a free Variable in the kit's own grammar, which — correctly, per the
    # documented lossiness — collapses to Constant on the way back; "alice"
    # sidesteps that so this can be a structural check).
    f = _P.parse("P(alice) ∧ ¬Q(alice)")
    text = to_smtlib(f)
    [back] = parse_smtlib(text)
    assert back == f


def test_quantified_with_equality_round_trip():
    # ∀x (P(x) → x = alice): textbook shape (a guarded universal ending in
    # an equality atom); the bound variable x is preserved exactly (Z3
    # Var/de-Bruijn round trip) and "alice" is already a Constant (see
    # test_propositional_round_trip's comment), so this is also a
    # structural check.
    f = _P.parse("∀x (P(x) → x = alice)")
    text = to_smtlib(f)
    [back] = parse_smtlib(text)
    assert back == f


def test_arithmetic_flavoured_round_trip():
    # x + 1 > 0, built directly (this exact shape is unreachable through the
    # kit's own grammar without a many-sorted/arithmetic mode, but a Node
    # like this is a legitimate input to to_z3()/to_smtlib all the same).
    # x is FREE here, so from_z3 reads it back as a Constant, not a
    # Variable (the documented free-variable lossiness) — checked via
    # logical equivalence rather than structural equality.
    #
    # RE-PINNED. The kit reads ``+`` and ``>`` here as UNINTERPRETED symbols,
    # and an export that declared them under those names (``(declare-fun + (S S)
    # S)``) is text a solver of the SMT-LIB theories cannot take: the default
    # logic is ALL, and cvc5 ends the Python process on it (see
    # test_cvc5_theory_symbols.py). A name of an SMT-LIB theory is therefore
    # renamed in the text, so what comes back is the formula over the RENAMED
    # symbols; the numerals 1 and 0 keep their names. The old expectation, that
    # the reread formula is equivalent to the original one over the SAME names,
    # only held because the theory names were written as they were.
    f = Atom(">", [Function("+", [Variable("x"), Number(1)]), Number(0)])
    text = to_smtlib(f)
    assert "(declare-fun + " not in text and "(declare-fun > " not in text
    [back] = parse_smtlib(text)
    # The tokens are what the sanitiser chose for the two symbols (its own name map, not read off ``back``):
    # the token of the predicate ``>`` stands in the predicate's place, the token of the function ``+`` in the
    # function's, the numerals keep their names, and a free x is the constant of that name (the text of a free
    # variable is a constant of its name, the documented lossiness). A text that exchanged the two tokens, or
    # put either in the other's place, is a different formula and fails here.
    _, names = _sanitize_many_for_smtlib([f])
    greater, plus = names.get(">"), names.get("+")
    assert greater != ">" and plus != "+" and greater != plus
    assert names.reverse()[greater] == ">" and names.reverse()[plus] == "+"
    assert back == Atom(greater, [Function(plus, [Constant("x"), Number(1)]), Number(0)])


def test_multi_premise_entailment_round_trip():
    # ∀x(P(x)→Q(x)), P(alice) ⊨ Q(alice): each premise and the goal come
    # back as their OWN top-level assertion, in order — not one folded
    # implication.
    premises = [_P.parse("∀x (P(x) → Q(x))"), _P.parse("P(alice)")]
    goal = _P.parse("Q(alice)")
    text = to_smtlib(goal, premises)
    nodes = parse_smtlib(text)
    assert len(nodes) == 3
    assert nodes[0] == premises[0]
    assert nodes[1] == premises[1]
    assert nodes[2] == goal


# ---------------------------------------------------------------------------
# Differential: the exported text, reparsed, must decide the SAME
# sat/unsat question as the kit's own to_z3() route asked directly.
# ---------------------------------------------------------------------------

def _z3_check_direct(premises, formula):
    """premises ∧ formula, built straight from Node.to_z3() — no SMT-LIB2
    text involved at all; the baseline the exported text is compared to."""
    solver = z3.Solver()
    for p in premises:
        solver.add(p.to_z3())
    solver.add(formula.to_z3())
    return solver.check()


def _z3_check_via_text(premises, formula):
    """The SAME question, but built by reparsing to_smtlib's own output."""
    text = to_smtlib(formula, premises)
    reparsed = list(z3.parse_smt2_string(text))
    solver = z3.Solver()
    for expr in reparsed:
        solver.add(expr)
    return solver.check()


def test_entailed_conclusion_is_sat_jointly_on_both_routes():
    # Modus-ponens instance: P(a) and Q(a) are jointly consistent with the
    # rule ∀x(P(x)→Q(x)) — a satisfying structure trivially exists (make
    # both P and Q true everywhere), so both routes must say sat.
    premises = [_P.parse("∀x (P(x) → Q(x))"), _P.parse("P(a)")]
    goal = _P.parse("Q(a)")
    assert _z3_check_direct(premises, goal) == z3.sat
    assert _z3_check_via_text(premises, goal) == z3.sat


def test_unrelated_premise_and_goal_are_jointly_sat_on_both_routes():
    # P(a) says nothing about Q, so P(a) ∧ Q(a) is satisfiable (and so is
    # P(a) ∧ ¬Q(a) — no link is asserted either way); pick the sat direction
    # and confirm the text round trip agrees with the direct route.
    premises = [_P.parse("P(a)")]
    goal = _P.parse("Q(a)")
    assert _z3_check_direct(premises, goal) == z3.sat
    assert _z3_check_via_text(premises, goal) == z3.sat


def test_contradiction_is_unsat_jointly_on_both_routes():
    # P(a) and ¬P(a) can never hold together in any structure.
    premises = [_P.parse("P(a)")]
    goal = _P.parse("¬P(a)")
    assert _z3_check_direct(premises, goal) == z3.unsat
    assert _z3_check_via_text(premises, goal) == z3.unsat


# ---------------------------------------------------------------------------
# Adversarial names — R1/R5-style, reusing the ground truth
# tests/test_cvc5_backend.py already established for these exact name
# shapes, extended here with the reserved-word case this task's review
# found and fixed.
# ---------------------------------------------------------------------------

class TestDigitLeadingName:
    def test_is_renamed_and_parses_via_z3(self):
        f = Atom("P", [Constant("2008SummerOlympics")])
        _, mapping = _sanitize_many_for_smtlib([f])
        token = mapping.mapping["2008SummerOlympics"]
        assert token != "2008SummerOlympics"
        assert token[0].isalpha()
        text = to_smtlib(f)
        z3.parse_smt2_string(text)   # must not raise

    def test_unsanitised_text_does_NOT_parse(self):
        # Negative control: the naive to_z3() + Solver.to_smt2() combination
        # this writer deliberately avoids, run WITHOUT the sanitiser, on the
        # exact same node — proves the positive test above exercises a real
        # fix, not a case that was never broken.
        f = Atom("P", [Constant("2008SummerOlympics")])
        solver = z3.Solver()
        solver.add(f.to_z3())
        with pytest.raises(z3.Z3Exception):
            z3.parse_smt2_string(solver.to_smt2())


class TestReservedWordName:
    def test_is_renamed_and_parses_via_z3(self):
        # "let" is a legal lower-case-initial NAME in the kit's own grammar
        # (predicate-hood needs an UPPER-case initial, which "let" cannot
        # carry) but an SMT-LIB2 <reserved> word — reachable as a predicate
        # name only via a programmatically built node (mirrors
        # test_cvc5_backend.py's TestDigitLeadingNamesNoLongerCrash's own
        # "2008Wins" predicate case for the same reason).
        f = Atom("let", [Constant("x")])
        _, mapping = _sanitize_many_for_smtlib([f])
        token = mapping.mapping["let"]
        assert token != "let"
        text = to_smtlib(f)
        z3.parse_smt2_string(text)   # must not raise

    def test_unsanitised_text_does_NOT_parse(self):
        # Negative control, same shape as the digit-leading one: Z3's own
        # to_smt2() does not quote "let" either (verified live), so an
        # uninterpreted predicate named "let" prints as the undecorated
        # head of "(let x)", which Z3's OWN parser then reads as the
        # let-BINDING form and rejects for lacking a binding list.
        f = Atom("let", [Constant("x")])
        solver = z3.Solver()
        solver.add(f.to_z3())
        with pytest.raises(z3.Z3Exception):
            z3.parse_smt2_string(solver.to_smt2())


class TestFiveReservedGrammarWordsStayUntouched:
    """Review finding, R1-style: SMT-LIB2 v2.6's grammar lists 13
    ``<reserved>`` words, but ``cvc5_backend._SMTLIB_RESERVED_WORDS`` (which
    ``to_smtlib`` inherits via ``_sanitize_many_for_smtlib``) only queues the
    7 Z3's own parser actually special-cases, and ``par``, which cvc5 reads as
    a keyword (RE-PINNED: this class used to hold ``par`` too, on Z3's word
    alone; cvc5 ends the Python process on a constant named ``par``, see
    test_cvc5_backend.py's ``TestSixReservedGrammarWordsZ3DoesNotSpecialCase``).
    These 5 (``BINARY``, ``DECIMAL``, ``HEXADECIMAL``, ``NUMERAL``,
    ``STRING``) already round-trip through Z3 with no help from this module,
    so ``to_smtlib`` must reproduce the ORIGINAL name through
    ``parse_smtlib``, not a synthesised ``n``-prefixed one — see
    test_cvc5_backend.py's ``TestSixReservedGrammarWordsZ3DoesNotSpecialCase``
    for the same claim checked directly against the shared sanitiser."""

    @pytest.mark.parametrize(
        "word", ["BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING"]
    )
    def test_round_trips_through_parse_smtlib_unrenamed(self, word):
        f = Atom("P", [Constant(word)])
        text = to_smtlib(f)
        [back] = parse_smtlib(text)
        assert back == f

    def test_par_is_written_under_a_token_cvc5_reads_as_a_symbol(self):
        f = Atom("P", [Constant("par")])
        text = to_smtlib(f)
        [back] = parse_smtlib(text)
        assert "(declare-fun par " not in text
        assert back == Atom("P", [Constant(back.args[0].name)]) and back.args[0].name != "par"


class TestNonAsciiName:
    def test_stays_untouched_and_round_trips_via_z3s_own_quoting(self):
        # R1 (test_cvc5_backend.py): a non-ASCII name already round-trips
        # through Z3's own automatic pipe-quoting correctly, so the shared
        # sanitiser must identity-map it, not rename something that already
        # worked.
        f = Atom("P", [Constant("świątek")])
        _, mapping = _sanitize_many_for_smtlib([f])
        assert mapping.mapping["świątek"] == "świątek"
        text = to_smtlib(f)
        [back] = parse_smtlib(text)
        assert back == f


# ---------------------------------------------------------------------------
# cvc5, where installed (oracle (c)): the exported text is also legal cvc5
# input, and cvc5 agrees with Z3 on a ground satisfiability question.
# ---------------------------------------------------------------------------

def test_cvc5_accepts_the_emitted_text_and_agrees_with_z3():
    cvc5 = pytest.importorskip("cvc5")

    # Ground (quantifier-free) on purpose: ordinary uninterpreted-sort UF is
    # decidable there, so neither engine can legitimately answer "unknown" —
    # a quantified example would risk cvc5's own instantiation heuristics
    # (see Cvc5Backend's class docstring: "unknown" is an honest outcome,
    # not a bug this test should be flaky against.) Also exercises a
    # digit-leading name in the same breath.
    formula = Atom("P", [Constant("2008SummerOlympics")])
    premises = [Atom("Q", [Constant("2008SummerOlympics")])]
    text = to_smtlib(formula, premises)

    assert _z3_check_direct(premises, formula) == z3.sat

    solver = cvc5.Solver()
    parser = cvc5.InputParser(solver)
    symbol_manager = parser.getSymbolManager()
    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, text,
                          "test_smtlib_export")
    while True:
        command = parser.nextCommand()
        if command.isNull():
            break
        if command.getCommandName() == "check-sat":
            continue
        command.invoke(solver, symbol_manager)
    assert solver.checkSat().isSat()


# ---------------------------------------------------------------------------
# Refusal: to_smtlib inherits to_z3's own out-of-fragment rejection
# verbatim, plus one appended sentence naming this entry point.
# ---------------------------------------------------------------------------

def test_second_order_formula_refuses_naming_the_construct():
    f = MSFLParser(second_order=True).parse("∃P P(a)")
    with pytest.raises(NotImplementedError, match="[Ss]econd-order"):
        to_smtlib(f)
    with pytest.raises(NotImplementedError, match="SMT-LIB2 export is first-order only"):
        to_smtlib(f)


def test_modal_formula_refuses_naming_the_construct():
    f = MSFLParser(modal=True).parse("□P")
    with pytest.raises(NotImplementedError, match="[Mm]odal"):
        to_smtlib(f)
    with pytest.raises(NotImplementedError, match="SMT-LIB2 export is first-order only"):
        to_smtlib(f)


def test_refusal_in_a_premise_also_refuses_the_whole_call():
    good = _P.parse("P(a)")
    bad = MSFLParser(second_order=True).parse("∃P P(a)")
    with pytest.raises(NotImplementedError):
        to_smtlib(good, [bad])


# ---------------------------------------------------------------------------
# Node.to_smtlib(): the single-formula convenience method.
# ---------------------------------------------------------------------------

def test_node_to_smtlib_matches_the_free_function_with_no_premises():
    f = _P.parse("P(a) ∧ ¬Q(a)")
    assert f.to_smtlib() == to_smtlib(f)


def test_node_to_smtlib_refuses_the_same_way_as_to_z3():
    f = MSFLParser(second_order=True).parse("∃P P(a)")
    with pytest.raises(NotImplementedError, match="[Ss]econd-order"):
        f.to_smtlib()


# ---------------------------------------------------------------------------
# The `logic` keyword.
# ---------------------------------------------------------------------------

def test_logic_keyword_controls_the_set_logic_line():
    f = _P.parse("P(a)")
    assert to_smtlib(f).startswith("(set-logic ALL)\n")
    assert to_smtlib(f, logic="UF").startswith("(set-logic UF)\n")
