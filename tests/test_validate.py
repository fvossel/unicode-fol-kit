"""Tests for unicode_fol_kit.eval.validate — well-formedness reports."""

from dataclasses import FrozenInstanceError

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Variable,
    Constant,
    Atom,
    And,
    Implies,
    Quantifier,
    Lambda,
    LambdaVar,
    Application,
    Function,
)
from unicode_fol_kit.eval.validate import (
    ValidationReport,
    validate,
    is_wellformed,
    validate_text,
)


# ---------------------------------------------------------------------------
# is_closed / free_variable_names
# ---------------------------------------------------------------------------

def test_is_closed_universal_sentence():
    """∀x P(x) is closed; free_variable_names is empty."""
    x = Variable("x")
    node = Quantifier("∀", x, Atom("P", [x]))
    report = validate(node)
    assert report.is_closed is True
    assert report.free_variable_names == ()


def test_not_closed_free_variable():
    """P(x) with x free is not closed; the free name is reported."""
    x = Variable("x")
    node = Atom("P", [x])
    report = validate(node)
    assert report.is_closed is False
    assert report.free_variable_names == ("x",)


def test_free_variable_names_sorted_and_deduplicated():
    """Multiple distinct free vars appear sorted and de-duplicated."""
    x, y = Variable("x"), Variable("y")
    # P(y) ∧-style implication mixing two free vars, x appears twice.
    node = Implies(Atom("P", [x, y]), Atom("Q", [x]))
    report = validate(node)
    assert report.free_variable_names == ("x", "y")
    assert report.is_closed is False


# ---------------------------------------------------------------------------
# arity consistency
# ---------------------------------------------------------------------------

def test_arity_conflict_same_predicate():
    """Mixing P/1 and P/2 makes arity inconsistent with a reported conflict."""
    x, y = Variable("x"), Variable("y")
    node = Implies(Atom("P", [x]), Atom("P", [x, y]))
    report = validate(node)
    assert report.arity_consistent is False
    assert report.arity_conflicts[("pred", "P")] == (1, 2)


def test_arity_consistent_when_uniform():
    """A formula using each symbol at one arity is arity-consistent."""
    x = Variable("x")
    node = Quantifier("∀", x, Implies(Atom("Human", [x]), Atom("Mortal", [x])))
    report = validate(node)
    assert report.arity_consistent is True
    assert report.arity_conflicts == {}


def test_predicate_and_function_same_name_no_conflict():
    """A predicate P/1 and a function p/2 sit in separate namespaces."""
    x, y = Variable("x"), Variable("y")
    # P(p(x, y)) — predicate "P"/1, function "p"/2; names differ in case but
    # even with identical text they would not collide across namespaces.
    func = Function("p", [x, y])
    node = Atom("P", [func])
    report = validate(node)
    assert report.arity_consistent is True
    assert report.arity_conflicts == {}

    # Identical textual name P used as both predicate/1 and function/2.
    func2 = Function("P", [x, y])
    node2 = Atom("P", [func2])
    report2 = validate(node2)
    assert report2.arity_consistent is True
    assert report2.arity_conflicts == {}
    assert "P/1" in report2.predicates
    assert "P/2" in report2.functions


# ---------------------------------------------------------------------------
# has_lambdas
# ---------------------------------------------------------------------------

def test_has_lambdas_true_before_elimination():
    """An application of λP. P(x) to Q (built directly) has lambdas."""
    lam = Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x")))
    node = Application(lam, LambdaVar("Q"))
    report = validate(node)
    assert report.has_lambdas is True


def test_has_lambdas_false_plain_formula():
    """A plain quantified formula has no lambda machinery."""
    x = Variable("x")
    node = Quantifier("∀", x, Atom("P", [x]))
    report = validate(node)
    assert report.has_lambdas is False


# ---------------------------------------------------------------------------
# is_wellformed
# ---------------------------------------------------------------------------

def test_is_wellformed_true():
    """∀x (Human(x) → Mortal(x)) is closed, arity-consistent, lambda-free."""
    x = Variable("x")
    node = Quantifier("∀", x, Implies(Atom("Human", [x]), Atom("Mortal", [x])))
    assert is_wellformed(node) is True


def test_is_wellformed_false_open():
    """An open formula is not well-formed."""
    node = Atom("P", [Variable("x")])
    assert is_wellformed(node) is False


def test_is_wellformed_false_lambdas():
    """A residual lambda makes a closed formula not well-formed."""
    node = Lambda(LambdaVar("P"), Application(LambdaVar("P"), Constant("a")))
    assert is_wellformed(node) is False


# ---------------------------------------------------------------------------
# validate_text
# ---------------------------------------------------------------------------

def test_validate_text_good_string_parseable():
    """A syntactically valid formula parses and validates."""
    report = validate_text("∀x (Human(x) → Mortal(x))")
    assert report.parseable is True
    assert report.error is None
    assert report.is_closed is True


def test_validate_text_unbalanced_not_parseable():
    """An unbalanced 'forall x (P(x)' fails to parse with a message."""
    report = validate_text("∀x (P(x)")
    assert report.parseable is False
    assert report.error is not None
    assert isinstance(report.error, str)
    assert report.error  # non-empty message


def test_validate_text_default_parser_is_fol():
    """validate_text with no parser uses classical FOL mode by default.

    A bare single letter parses as a variable, so a multi-letter NAME is used
    to land an actual Constant in the inventory.
    """
    report = validate_text("P(alice)")
    assert report.parseable is True
    assert "alice" in report.constants


# ---------------------------------------------------------------------------
# inventories on an MSFOL example
# ---------------------------------------------------------------------------

def test_inventories_on_msfol_example():
    """predicates / functions / constants / sorts are populated correctly."""
    parser = MSFLParser(many_sorted=True)
    # Sorted universal over Human; body references a function foo (function
    # names must be multi-letter, since a single lowercase letter is a variable).
    node = parser.parse("∀x:Human (Mortal(x) → Knows(x, foo(x)))")
    report = validate(node)

    assert report.parseable is True
    assert report.is_closed is True
    assert "Mortal/1" in report.predicates
    assert "Knows/2" in report.predicates
    assert "foo/1" in report.functions
    assert "Human" in report.sorts_used


def test_inventories_constants_and_sorted_constant():
    """SortedConstant contributes both a constant name and a sort."""
    parser = MSFLParser(many_sorted=True)
    node = parser.parse("Mortal(alice:Human)")
    report = validate(node)
    assert "alice" in report.constants
    assert "Human" in report.sorts_used
    assert "Mortal/1" in report.predicates


# ---------------------------------------------------------------------------
# report shape / repr
# ---------------------------------------------------------------------------

def test_report_is_frozen():
    """ValidationReport is an immutable (frozen) dataclass."""
    report = validate(Atom("P", [Constant("a")]))
    assert isinstance(report, ValidationReport)
    try:
        report.is_closed = False  # type: ignore[misc]
        assert False, "expected FrozenInstanceError"
    except FrozenInstanceError:
        pass


# ---------------------------------------------------------------------------
# adversarial review: arity-namespace edges, lambda-var freeness, parser
# injection, builtin exclusion (gaps not covered by the baseline suite)
# ---------------------------------------------------------------------------

def test_nullary_vs_unary_predicate_conflicts():
    """A nullary P() (arity 0) and P/1 are distinct arities -> a real conflict."""
    x = Variable("x")
    node = And(Atom("P", []), Atom("P", [x]))
    report = validate(node)
    assert report.arity_consistent is False
    assert report.arity_conflicts[("pred", "P")] == (0, 1)
    # The inventory shows BOTH forms seen.
    assert "P/0" in report.predicates
    assert "P/1" in report.predicates


def test_function_two_arities_conflict_and_inventory():
    """A function f used at /1 and /2 conflicts and lists both forms."""
    x, y = Variable("x"), Variable("y")
    node = And(Atom("Q", [Function("f", [x])]),
               Atom("Q", [Function("f", [x, y])]))
    report = validate(node)
    assert report.arity_conflicts[("func", "f")] == (1, 2)
    assert "f/1" in report.functions and "f/2" in report.functions
    # Q itself is used consistently at /1, so the only conflict is the function.
    assert ("pred", "Q") not in report.arity_conflicts


def test_free_lambda_var_breaks_closedness_and_is_named():
    """A free LambdaVar counts against closedness and shows in free names."""
    # F is applied but never lambda-bound, so it is a FREE LambdaVar.
    node = Application(LambdaVar("F"), Constant("a"))
    report = validate(node)
    assert report.is_closed is False
    assert report.free_variable_names == ("F",)
    assert report.has_lambdas is True


def test_free_var_and_lambda_var_same_name_dedup():
    """A free Variable x and a free LambdaVar x collapse to a single name."""
    node = And(Atom("P", [Variable("x")]),
               Application(LambdaVar("x"), Constant("a")))
    report = validate(node)
    assert report.free_variable_names == ("x",)


def test_validate_text_accepts_injected_parser():
    """validate_text honours an explicitly injected (sorted) parser."""
    parser = MSFLParser(many_sorted=True)
    report = validate_text("Mortal(alice:Human)", parser=parser)
    assert report.parseable is True
    assert "alice" in report.constants
    assert "Human" in report.sorts_used


def test_builtin_operators_excluded_from_inventory_and_arity():
    """Comparison (=) and arithmetic (+) symbols are not user symbols."""
    node = MSFLParser().parse("∀x (x = x ∧ P(x + x))")
    report = validate(node)
    # "=" and "+" appear nowhere in the inventories.
    assert all(not p.startswith("=") for p in report.predicates)
    assert all(not f.startswith("+") for f in report.functions)
    assert "P/1" in report.predicates
    # Builtins never trigger an arity conflict even though = is used /2.
    assert report.arity_consistent is True


def test_is_wellformed_false_on_arity_conflict():
    """A closed, lambda-free formula with an arity clash is not well-formed."""
    x, y = Variable("x"), Variable("y")
    node = Quantifier("∀", x, And(Atom("P", [x]), Atom("P", [x, y])))
    # Closed (x, y both bound? y is free) — make it genuinely closed:
    closed = Quantifier("∀", x, Quantifier("∀", y,
                        And(Atom("P", [x]), Atom("P", [x, y]))))
    report = validate(closed)
    assert report.is_closed is True
    assert report.has_lambdas is False
    assert report.arity_consistent is False
    assert is_wellformed(closed) is False


def test_validate_text_namingerror_path_unparseable():
    """A stray illegal character is caught (lexer NamingError) not raised."""
    report = validate_text("∀x (P(x)) @")
    assert report.parseable is False
    assert report.error and isinstance(report.error, str)


def test_report_str_is_readable():
    """str(report) yields a multi-line human-readable summary."""
    report = validate(Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])))
    text = str(report)
    assert "ValidationReport(" in text
    assert "is_closed" in text


def test_report_str_for_unparseable():
    """A non-parseable report stringifies compactly with the error."""
    report = validate_text("∀x (P(x)")
    text = str(report)
    assert "parseable=False" in text
