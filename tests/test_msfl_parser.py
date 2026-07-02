"""Tests for MSFLParser across FOL, MSFOL, and MSFL modes."""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.naming import NamingError, ParsingError
from unicode_fol_kit.fol._fol_nodes import (
    And, Or, Xor, Not, Implies, Iff, Quantifier,
    Atom, Variable, Constant, Number, Function,
)
from unicode_fol_kit.fol._msfl_nodes import (
    SortedQuantifier, SortedConstant,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)


# ---------------------------------------------------------------------------
# Construction
# ---------------------------------------------------------------------------

class TestConstruction:
    def test_default_constructs(self):
        p = MSFLParser()
        assert p._mode == "fol"

    def test_fol_explicit(self):
        p = MSFLParser(many_sorted=False, fuzzy=False)
        assert p._mode == "fol"

    def test_msfol_mode(self):
        p = MSFLParser(many_sorted=True, fuzzy=False)
        assert p._mode == "msfol"

    def test_msfl_mode(self):
        p = MSFLParser(many_sorted=True, fuzzy=True)
        assert p._mode == "msfl"

    def test_fl_mode_constructs(self):
        p = MSFLParser(many_sorted=False, fuzzy=True)
        assert p._mode == "fl"

    def test_all_four_modes_construct(self):
        # No flag combination is invalid; all four produce the expected _mode string.
        expected = {
            (False, False): "fol",
            (True,  False): "msfol",
            (True,  True):  "msfl",
            (False, True):  "fl",
        }
        for (ms, fz), mode in expected.items():
            p = MSFLParser(many_sorted=ms, fuzzy=fz)
            assert p._mode == mode, f"many_sorted={ms}, fuzzy={fz}: expected {mode!r}, got {p._mode!r}"


# ---------------------------------------------------------------------------
# FOL mode
# ---------------------------------------------------------------------------

class TestFOLMode:
    @pytest.fixture(autouse=True)
    def parser(self):
        self.p = MSFLParser()

    def test_atom_with_arg(self):
        result = self.p.parse("P(x)")
        assert result == Atom("P", [Variable("x")])

    def test_atom_zero_arity(self):
        result = self.p.parse("P")
        assert result == Atom("P", [])

    def test_and(self):
        result = self.p.parse("P(x) ∧ Q(y)")
        assert type(result) is And

    def test_or(self):
        result = self.p.parse("P(x) ∨ Q(y)")
        assert type(result) is Or

    def test_xor(self):
        result = self.p.parse("P(x) ⊕ Q(y)")
        assert type(result) is Xor

    def test_not(self):
        result = self.p.parse("¬P(x)")
        assert result == Not(Atom("P", [Variable("x")]))

    def test_implies(self):
        result = self.p.parse("P(x) → Q(y)")
        assert type(result) is Implies

    def test_iff(self):
        result = self.p.parse("P(x) ↔ Q(y)")
        assert type(result) is Iff

    def test_forall(self):
        result = self.p.parse("∀x P(x)")
        assert isinstance(result, Quantifier)
        assert result.type == "∀"
        assert result.variable == Variable("x")

    def test_exists(self):
        result = self.p.parse("∃x P(x)")
        assert isinstance(result, Quantifier)
        assert result.type == "∃"

    def test_constant_name(self):
        result = self.p.parse("P(alice)")
        assert result == Atom("P", [Constant("alice")])

    def test_constant_c_prefix(self):
        result = self.p.parse("P(c_foo)")
        assert result == Atom("P", [Constant("c_foo")])

    def test_integer_number(self):
        result = self.p.parse("x = 42")
        assert result == Atom("=", [Variable("x"), Number(42)])

    def test_float_number(self):
        result = self.p.parse("x = 3.14")
        assert result == Atom("=", [Variable("x"), Number(3.14)])

    def test_infix_lt(self):
        assert self.p.parse("x < y") == Atom("<", [Variable("x"), Variable("y")])

    def test_infix_gt(self):
        assert self.p.parse("x > y") == Atom(">", [Variable("x"), Variable("y")])

    def test_infix_eq(self):
        assert self.p.parse("x = y") == Atom("=", [Variable("x"), Variable("y")])

    def test_infix_le(self):
        assert self.p.parse("x ≤ y") == Atom("≤", [Variable("x"), Variable("y")])

    def test_infix_ge(self):
        assert self.p.parse("x ≥ y") == Atom("≥", [Variable("x"), Variable("y")])

    def test_infix_ne(self):
        assert self.p.parse("x ≠ y") == Atom("≠", [Variable("x"), Variable("y")])

    def test_and_left_fold(self):
        result = self.p.parse("P(x) ∧ Q(y) ∧ R(z)")
        assert type(result) is And
        assert type(result.left) is And  # left-associative

    def test_or_left_fold(self):
        result = self.p.parse("P(x) ∨ Q(y) ∨ R(z)")
        assert type(result) is Or
        assert type(result.left) is Or

    def test_xor_left_fold(self):
        result = self.p.parse("P(x) ⊕ Q(y) ⊕ R(z)")
        assert type(result) is Xor
        assert type(result.left) is Xor

    def test_parentheses(self):
        result = self.p.parse("(P(x) ∧ Q(x)) → R(x)")
        assert type(result) is Implies
        assert type(result.left) is And

    def test_brackets(self):
        result = self.p.parse("[P(x) ∧ Q(x)] → R(x)")
        assert type(result) is Implies
        assert type(result.left) is And

    def test_nested_quantifiers(self):
        result = self.p.parse("∀x ∃y P(x, y)")
        assert isinstance(result, Quantifier)
        assert isinstance(result.formula, Quantifier)

    def test_arithmetic_add(self):
        result = self.p.parse("x + y = z")
        assert result == Atom("=", [Function("+", [Variable("x"), Variable("y")]), Variable("z")])

    def test_arithmetic_sub(self):
        result = self.p.parse("x - y = z")
        assert result == Atom("=", [Function("-", [Variable("x"), Variable("y")]), Variable("z")])

    def test_arithmetic_mul(self):
        result = self.p.parse("x * y = z")
        assert result == Atom("=", [Function("*", [Variable("x"), Variable("y")]), Variable("z")])

    def test_arithmetic_div(self):
        result = self.p.parse("x / y = z")
        assert result == Atom("=", [Function("/", [Variable("x"), Variable("y")]), Variable("z")])

    def test_right_associative_implies(self):
        result = self.p.parse("P(x) → Q(x) → R(x)")
        assert type(result) is Implies
        assert type(result.right) is Implies

    def test_right_associative_iff(self):
        result = self.p.parse("P(x) ↔ Q(x) ↔ R(x)")
        assert type(result) is Iff
        assert type(result.right) is Iff


# ---------------------------------------------------------------------------
# MSFOL mode
# ---------------------------------------------------------------------------

class TestMSFOLMode:
    @pytest.fixture(autouse=True)
    def parser(self):
        self.p = MSFLParser(many_sorted=True)

    def test_sorted_forall(self):
        result = self.p.parse("∀x :Human P(x)")
        assert isinstance(result, SortedQuantifier)
        assert result.type == "∀"
        assert result.variable == Variable("x")
        assert result.sort == "Human"  # colon stripped

    def test_sorted_exists(self):
        result = self.p.parse("∃x :Animal P(x)")
        assert isinstance(result, SortedQuantifier)
        assert result.type == "∃"
        assert result.sort == "Animal"

    def test_sorted_const_name(self):
        result = self.p.parse("P(alice :Human)")
        assert isinstance(result, Atom)
        assert result.args[0] == SortedConstant("alice", "Human")

    def test_sorted_const_c_prefix(self):
        result = self.p.parse("P(c_foo :Sort1)")
        assert isinstance(result, Atom)
        assert result.args[0] == SortedConstant("c_foo", "Sort1")

    def test_sort_colon_stripped(self):
        q = self.p.parse("∀x :Human P(x)")
        assert q.sort == "Human"
        assert not q.sort.startswith(":")

    def test_sorted_forall_no_space(self):
        result = self.p.parse("∀x:Human P(x)")
        assert isinstance(result, SortedQuantifier)
        assert result.sort == "Human"

    def test_sorted_const_name_no_space(self):
        result = self.p.parse("P(alice:Human)")
        assert isinstance(result, Atom)
        assert result.args[0] == SortedConstant("alice", "Human")

    def test_and(self):
        result = self.p.parse("P(x) ∧ Q(y)")
        assert type(result) is And

    def test_or(self):
        result = self.p.parse("P(x) ∨ Q(y)")
        assert type(result) is Or

    def test_not(self):
        result = self.p.parse("¬P(x)")
        assert type(result) is Not

    def test_implies(self):
        result = self.p.parse("P(x) → Q(y)")
        assert type(result) is Implies

    def test_iff(self):
        result = self.p.parse("P(x) ↔ Q(y)")
        assert type(result) is Iff

    def test_xor_accepted(self):
        # MSFOL is classical, so ⊕ is Xor (as in fol/modal/second-order); the glyph
        # is Łukasiewicz strong disjunction only in the fuzzy modes.
        result = self.p.parse("P(x) ⊕ Q(y)")
        assert type(result) is Xor

    def test_unsorted_quantifier_rejected(self):
        with pytest.raises((NamingError, ParsingError)):
            self.p.parse("∀x P(x)")

    def test_unsorted_constant_rejected(self):
        with pytest.raises((NamingError, ParsingError)):
            self.p.parse("P(alice)")

    def test_nested_sorted_quantifiers(self):
        result = self.p.parse("∀x :Human ∃y :Animal P(x, y)")
        assert isinstance(result, SortedQuantifier)
        assert isinstance(result.formula, SortedQuantifier)
        assert result.sort == "Human"
        assert result.formula.sort == "Animal"

    def test_complex_sorted_formula(self):
        # quantifier is at negation level, so ∀x:Human body → R parses as (∀x:Human body) → R
        result = self.p.parse("∀x :Human (P(x) ∧ ¬Q(x)) → R(x)")
        assert type(result) is Implies
        assert isinstance(result.left, SortedQuantifier)
        assert isinstance(result.left.formula, And)


# ---------------------------------------------------------------------------
# MSFL mode
# ---------------------------------------------------------------------------

class TestMSFLMode:
    @pytest.fixture(autouse=True)
    def parser(self):
        self.p = MSFLParser(many_sorted=True, fuzzy=True)

    def test_sorted_forall(self):
        result = self.p.parse("∀x :Human P(x)")
        assert isinstance(result, SortedQuantifier)
        assert result.sort == "Human"

    def test_sorted_const(self):
        result = self.p.parse("P(alice :Human)")
        assert result.args[0] == SortedConstant("alice", "Human")

    def test_sorted_forall_no_space(self):
        result = self.p.parse("∀x:Human P(x)")
        assert isinstance(result, SortedQuantifier)
        assert result.sort == "Human"

    def test_sorted_const_no_space(self):
        result = self.p.parse("P(alice:Human)")
        assert result.args[0] == SortedConstant("alice", "Human")

    def test_weak_and(self):
        result = self.p.parse("P(x) ∧ Q(y)")
        assert type(result) is WeakConjunction

    def test_weak_or(self):
        result = self.p.parse("P(x) ∨ Q(y)")
        assert type(result) is WeakDisjunction

    def test_strong_and(self):
        result = self.p.parse("P(x) ⊗ Q(y)")
        assert type(result) is StrongConjunction

    def test_strong_or(self):
        result = self.p.parse("P(x) ⊕ Q(y)")
        assert type(result) is StrongDisjunction

    def test_luk_not(self):
        result = self.p.parse("¬P(x)")
        assert type(result) is LukNegation

    def test_luk_implies(self):
        result = self.p.parse("P(x) → Q(y)")
        assert type(result) is LukImplication

    def test_luk_iff(self):
        result = self.p.parse("P(x) ↔ Q(y)")
        assert type(result) is LukEquivalence

    def test_xor_symbol_is_strong_disjunction(self):
        # In MSFL mode, ⊕ is strong disjunction, NOT classical Xor
        result = self.p.parse("P(x) ⊕ Q(y)")
        assert type(result) is StrongDisjunction
        assert type(result) is not Xor

    def test_weak_and_left_fold(self):
        result = self.p.parse("P(x) ∧ Q(y) ∧ R(z)")
        assert type(result) is WeakConjunction
        assert type(result.left) is WeakConjunction

    def test_strong_and_left_fold(self):
        result = self.p.parse("P(x) ⊗ Q(y) ⊗ R(z)")
        assert type(result) is StrongConjunction
        assert type(result.left) is StrongConjunction

    def test_complex_formula(self):
        result = self.p.parse("(P(x) ∧ Q(x)) → ¬R(x)")
        assert type(result) is LukImplication
        assert type(result.left) is WeakConjunction
        assert type(result.right) is LukNegation

    def test_nested_sorted_quantifiers(self):
        result = self.p.parse("∀x :Human ∃y :Animal P(x, y)")
        assert isinstance(result, SortedQuantifier)
        assert isinstance(result.formula, SortedQuantifier)

    def test_unsorted_quantifier_rejected(self):
        with pytest.raises((NamingError, ParsingError)):
            self.p.parse("∀x P(x)")

    def test_unsorted_constant_rejected(self):
        with pytest.raises((NamingError, ParsingError)):
            self.p.parse("P(alice)")

    def test_luk_right_assoc_iff(self):
        result = self.p.parse("P(x) ↔ Q(x) ↔ R(x)")
        assert type(result) is LukEquivalence
        assert type(result.right) is LukEquivalence


# ---------------------------------------------------------------------------
# Mixing errors (mode-aware hints)
# ---------------------------------------------------------------------------

class TestMixingErrors:
    def _error_str(self, parser, formula):
        with pytest.raises((NamingError, ParsingError)) as exc_info:
            parser.parse(formula)
        return str(exc_info.value)

    def test_fol_mixing_hint_contains_xor(self):
        msg = self._error_str(MSFLParser(), "P(x) ∧ Q(y) ∨ R(z)")
        assert "exclusive or" in msg or "mix" in msg

    def test_fol_mixing_hint_mentions_exclusive_or(self):
        msg = self._error_str(MSFLParser(), "P(x) ∧ Q(y) ⊕ R(z)")
        assert "exclusive or" in msg

    def test_msfol_mixing_hint_no_exclusive_or(self):
        p = MSFLParser(many_sorted=True)
        # In MSFOL mode, ⊕ isn't even in the grammar, but ∧/∨ mixing is the error
        msg = self._error_str(p, "P(x) ∧ Q(y) ∨ R(z)")
        assert "exclusive or" not in msg
        assert "mix" in msg or "conjunction" in msg

    def test_msfol_mixing_hint_text(self):
        p = MSFLParser(many_sorted=True)
        msg = self._error_str(p, "P(x) ∧ Q(y) ∨ R(z)")
        assert "conjunction" in msg
        assert "disjunction" in msg

    def test_msfl_mixing_hint_mentions_strong(self):
        p = MSFLParser(many_sorted=True, fuzzy=True)
        msg = self._error_str(p, "P(x) ∧ Q(y) ⊗ R(z)")
        assert "strong conjunction" in msg

    def test_msfl_mixing_hint_all_four_operators(self):
        p = MSFLParser(many_sorted=True, fuzzy=True)
        msg = self._error_str(p, "P(x) ∧ Q(y) ⊗ R(z)")
        assert "weak conjunction" in msg
        assert "weak disjunction" in msg
        assert "strong conjunction" in msg
        assert "strong disjunction" in msg

    def test_fol_raises_naming_or_parsing_error(self):
        with pytest.raises((NamingError, ParsingError)):
            MSFLParser().parse("P(x) ∧ Q(y) ∨ R(z)")

    def test_incomplete_formula_raises_parsing_error(self):
        with pytest.raises(ParsingError):
            MSFLParser().parse("P(x) →")


# ---------------------------------------------------------------------------
# Lambda syntax (subtask 4a)
# ---------------------------------------------------------------------------

class TestLambdaSyntax:
    """Lambda-abstraction and application parsing across all three modes.

    parse() auto-applies resolve_lambda_scope, so all assertions reflect the
    fully scope-resolved AST: body Variables whose name is lambda-bound become
    LambdaVar, and body Atoms whose predicate is lambda-bound become Application.
    """

    # -- Spike confirmation: existing rules unaffected --

    def test_existing_atom_still_parses_fol(self):
        # P(x) must parse as Atom, not Application, under the new grammar.
        result = MSFLParser().parse("P(x)")
        assert isinstance(result, Atom)
        assert result.predicate == "P"
        assert result.args == (Variable("x"),)

    def test_existing_conjunction_unaffected(self):
        result = MSFLParser().parse("P(x) ∧ Q(y)")
        assert isinstance(result, And)
        assert isinstance(result.left, Atom)
        assert isinstance(result.right, Atom)

    # -- FOL mode --

    def test_fol_lambda_variable_param(self):
        # λx. P(x) → Lambda(LambdaVar("x"), Atom("P", [LambdaVar("x")]))
        # x is lambda-bound, so body arg x becomes LambdaVar; P is not bound → stays Atom.
        result = MSFLParser().parse("λx. P(x)")
        assert isinstance(result, Lambda)
        assert isinstance(result.param, LambdaVar)
        assert result.param.name == "x"
        assert result.body == Atom("P", [LambdaVar("x")])

    def test_fol_lambda_predicate_param(self):
        # λP. P(x) → Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x")))
        # P is lambda-bound → body Atom("P", [Variable("x")]) becomes Application.
        # x is NOT lambda-bound → stays Variable.
        result = MSFLParser().parse("λP. P(x)")
        assert isinstance(result, Lambda)
        assert isinstance(result.param, LambdaVar)
        assert result.param.name == "P"
        assert isinstance(result.body, Application)
        assert result.body.func == LambdaVar("P")
        assert result.body.arg == Variable("x")

    def test_fol_nested_lambda(self):
        # λP. λx. P(x) — both P and x are lambda-bound in the inner body.
        # Scope at inner body: {P, x}. P(x) → Application(LambdaVar("P"), LambdaVar("x")).
        result = MSFLParser().parse("λP. λx. P(x)")
        assert isinstance(result, Lambda)
        assert result.param == LambdaVar("P")
        inner = result.body
        assert isinstance(inner, Lambda)
        assert inner.param == LambdaVar("x")
        assert inner.body == Application(LambdaVar("P"), LambdaVar("x"))

    def test_fol_lambda_body_extends_past_conjunction(self):
        # λx. P(x) ∧ Q(x) → Lambda with And body (formula-level precedence)
        result = MSFLParser().parse("λx. P(x) ∧ Q(x)")
        assert isinstance(result, Lambda)
        assert result.param == LambdaVar("x")
        assert isinstance(result.body, And)
        assert isinstance(result.body.left, Atom)
        assert isinstance(result.body.right, Atom)

    def test_fol_application_variable_arg(self):
        # (λx. P(x))(a) — 'a' is single letter → VARIABLE → Variable("a")
        result = MSFLParser().parse("(λx. P(x))(a)")
        assert isinstance(result, Application)
        assert isinstance(result.func, Lambda)
        assert result.func.param == LambdaVar("x")
        assert isinstance(result.arg, Variable)
        assert result.arg.name == "a"

    def test_fol_application_name_arg(self):
        # (λx. P(x))(alice) — 'alice' is NAME (multi-letter) → Constant("alice")
        result = MSFLParser().parse("(λx. P(x))(alice)")
        assert isinstance(result, Application)
        assert isinstance(result.arg, Constant)
        assert result.arg.name == "alice"

    def test_fol_application_atom_arg(self):
        # (λP. P(x))(Q) — arg 'Q' is PREDICATE → atom0_ → Atom("Q", [])
        result = MSFLParser().parse("(λP. P(x))(Q)")
        assert isinstance(result, Application)
        assert isinstance(result.arg, Atom)
        assert result.arg.predicate == "Q"
        assert result.arg.args == ()

    def test_fol_lambda_param_is_always_lambdavar(self):
        # Confirm param is LambdaVar regardless of which terminal class the name falls into.
        for src, expected_name in [("λx. P(x)", "x"), ("λP. P(x)", "P"), ("λfoo. P(x)", "foo")]:
            result = MSFLParser().parse(src)
            assert isinstance(result.param, LambdaVar), f"param not LambdaVar for {src!r}"
            assert result.param.name == expected_name

    # -- MSFOL mode --

    def test_msfol_lambda_variable_param(self):
        result = MSFLParser(many_sorted=True).parse("λx. P(x)")
        assert isinstance(result, Lambda)
        assert result.param == LambdaVar("x")
        assert result.body == Atom("P", [LambdaVar("x")])

    def test_msfol_application_variable_arg(self):
        # MSFOL requires sort on named constants; use VARIABLE 'y' as arg.
        result = MSFLParser(many_sorted=True).parse("(λx. P(x))(y)")
        assert isinstance(result, Application)
        assert result.func.param == LambdaVar("x")
        assert result.arg == Variable("y")

    def test_msfol_lambda_predicate_param(self):
        result = MSFLParser(many_sorted=True).parse("λP. P(x)")
        assert isinstance(result, Lambda)
        assert result.param == LambdaVar("P")
        assert isinstance(result.body, Application)
        assert result.body.func == LambdaVar("P")
        assert result.body.arg == Variable("x")

    # -- MSFL mode --

    def test_msfl_lambda_variable_param(self):
        result = MSFLParser(many_sorted=True, fuzzy=True).parse("λx. P(x)")
        assert isinstance(result, Lambda)
        assert result.param == LambdaVar("x")
        assert result.body == Atom("P", [LambdaVar("x")])

    def test_msfl_lambda_strong_conjunction_body(self):
        # λx. P(x) ⊗ Q(x) → Lambda body is StrongConjunction (mode-specific operator)
        result = MSFLParser(many_sorted=True, fuzzy=True).parse("λx. P(x) ⊗ Q(x)")
        assert isinstance(result, Lambda)
        assert result.param == LambdaVar("x")
        assert isinstance(result.body, StrongConjunction)
        assert isinstance(result.body.left, Atom)
        assert isinstance(result.body.right, Atom)

    def test_msfl_lambda_predicate_param(self):
        result = MSFLParser(many_sorted=True, fuzzy=True).parse("λP. P(x)")
        assert isinstance(result, Lambda)
        assert result.param == LambdaVar("P")
        assert isinstance(result.body, Application)
        assert result.body.func == LambdaVar("P")
        assert result.body.arg == Variable("x")


# ---------------------------------------------------------------------------
# FL mode  (many_sorted=False, fuzzy=True)
# ---------------------------------------------------------------------------

class TestFLMode:
    """FL mode: Łukasiewicz operators with unsorted (FOL-style) quantifiers and constants."""

    @pytest.fixture(autouse=True)
    def parser(self):
        self.p = MSFLParser(many_sorted=False, fuzzy=True)

    # -- Łukasiewicz connectives --

    def test_luk_negation(self):
        result = self.p.parse("¬P(x)")
        assert isinstance(result, LukNegation)
        assert result.formula == Atom("P", [Variable("x")])

    def test_weak_conjunction(self):
        result = self.p.parse("P(x) ∧ Q(x)")
        assert isinstance(result, WeakConjunction)

    def test_weak_disjunction(self):
        result = self.p.parse("P(x) ∨ Q(x)")
        assert isinstance(result, WeakDisjunction)

    def test_strong_conjunction(self):
        result = self.p.parse("P(x) ⊗ Q(x)")
        assert isinstance(result, StrongConjunction)

    def test_strong_disjunction(self):
        result = self.p.parse("P(x) ⊕ Q(x)")
        assert isinstance(result, StrongDisjunction)

    def test_luk_implication(self):
        result = self.p.parse("P(x) → Q(x)")
        assert isinstance(result, LukImplication)

    def test_luk_equivalence(self):
        result = self.p.parse("P(x) ↔ Q(x)")
        assert isinstance(result, LukEquivalence)

    # -- Unsorted quantifiers (FOL-style, not SortedQuantifier) --

    def test_forall_unsorted(self):
        result = self.p.parse("∀x P(x)")
        assert isinstance(result, Quantifier)
        assert not isinstance(result, SortedQuantifier)
        assert result.type == "∀"
        assert result.variable == Variable("x")
        assert result.formula == Atom("P", [Variable("x")])

    def test_exists_unsorted(self):
        result = self.p.parse("∃x P(x)")
        assert isinstance(result, Quantifier)
        assert not isinstance(result, SortedQuantifier)
        assert result.type == "∃"

    # -- Unsorted constants (no sort annotation) --

    def test_plain_constant(self):
        result = self.p.parse("P(alice)")
        assert result == Atom("P", [Constant("alice")])

    # -- Rejection of sort syntax (SORT not in FL grammar) --

    def test_rejects_sorted_quantifier(self):
        with pytest.raises((NamingError, ParsingError)):
            self.p.parse("∀x:Human P(x)")

    def test_rejects_sorted_constant(self):
        with pytest.raises((NamingError, ParsingError)):
            self.p.parse("P(alice:Human)")

    # -- ⊕ is StrongDisjunction in FL, NOT the classical Xor of the crisp modes --

    def test_strong_disjunction_not_xor(self):
        result = self.p.parse("P(x) ⊕ Q(x)")
        assert isinstance(result, StrongDisjunction)
        assert not isinstance(result, Xor)

    # -- Operator-mixing error carries the MSFL-style hint --

    def test_mixing_hint(self):
        # Mixing ∧ and ⊗ triggers a lexer-level NamingError in FL (the ⊗ is unexpected
        # after a partial only_weak_and sequence) — the hint text is the same as MSFL.
        with pytest.raises((NamingError, ParsingError)) as exc_info:
            self.p.parse("P(x) ∧ Q(x) ⊗ R(x)")
        msg = str(exc_info.value)
        assert "weak conjunction" in msg
        assert "strong conjunction" in msg

    # -- Lambda syntax in FL --

    def test_lambda_in_fl(self):
        # λx. P(x) ⊗ Q(x) → Lambda, body StrongConjunction, x scope-resolved to LambdaVar
        result = self.p.parse("λx. P(x) ⊗ Q(x)")
        assert isinstance(result, Lambda)
        assert result.param == LambdaVar("x")
        assert isinstance(result.body, StrongConjunction)
        assert result.body.left == Atom("P", [LambdaVar("x")])
        assert result.body.right == Atom("Q", [LambdaVar("x")])
