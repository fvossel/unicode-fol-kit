"""Exhaustive LaTeX round-trip battery: parse_latex(ast.to_latex(), <mode>) == ast
for EVERY operator the toolkit knows how to render to LaTeX.

Three tiers of coverage:

* REGISTRY-DRIVEN completeness pin — every ``OperatorSpec`` registered in
  ``unicode_fol_kit.fol._fol_nodes.OPERATORS`` (the table ``to_latex`` /
  ``to_unicode_str`` read to render a connective) must have an entry in
  ``_OPERATOR_BATTERY`` below. If a new operator is registered without adding
  a battery entry, ``test_battery_covers_every_registered_operator`` fails —
  this is the "nothing new can silently go unrounded" guarantee.
* NON-REGISTRY constructs — binders and terms with their own explicit branch
  in the ``_uni`` / ``_latex`` renderers (Count, Cardinality, Measure,
  Nominal, Dependence, SlashedExists, One, Lambda, Application, the three
  quantifier flavours) are not registry-driven, so they get their own
  (manually enumerated, but still exhaustive over every such construct in
  ``_msfl_nodes.py``'s renderer dispatch) battery.
* The single-letter (VARIABLE-headed) function-call grammar fix gets its own
  small pinned suite at the bottom.

This file complements (does not replace) ``tests/test_latex_input.py``, which
covers hand-written LaTeX synonyms/spacing and a curated set of nested/mixed
formulas; this file's job is exhaustive per-operator coverage.
"""

import pytest

from unicode_fol_kit.fol._fol_nodes import OPERATORS
from unicode_fol_kit.fol.latex_input import latex_to_unicode, parse_latex
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import Atom, Function, Variable


# ---------------------------------------------------------------------------
# Mode-kwargs shorthands (mirrors tests/test_latex_input.py).
# ---------------------------------------------------------------------------

_FOL = {}
_MSFOL = {"many_sorted": True}
_FL = {"fuzzy": True}
_MODAL = {"modal": True}
_SO = {"second_order": True}
_DEP = {"dependence": True}
_LIN = {"linear": True}
_LAM = {"lambek": True}


# ---------------------------------------------------------------------------
# Tier 1 — every registry operator (OPERATORS), one representative formula
# each, in a mode where it is registered (see parser_ops_for_mode).
# ---------------------------------------------------------------------------
#
# Each source string is plain Unicode surface syntax; the ground-truth AST is
# built by parsing it in the SAME mode the round trip re-parses in, exactly
# like tests/test_latex_input.py's _ROUND_TRIP table.

_OPERATOR_BATTERY = {
    # Classical connectives (fol; also registered for msfol/modal/so/dependence,
    # one representative mode suffices here).
    "And": ("P ∧ Q", _FOL),
    "Or": ("P ∨ Q", _FOL),
    "Xor": ("P ⊕ Q", _FOL),
    "Not": ("¬P", _FOL),
    "Implies": ("P → Q", _FOL),
    "Iff": ("P ↔ Q", _FOL),
    "Contrast": ("P Ⓒ Q", _FOL),
    # Hybrid logic (modal mode only).
    "At": ("@i P", _MODAL),
    # Modal / epistemic / doxastic / deontic / temporal (modal mode only).
    "Box": ("□P", _MODAL),
    "Diamond": ("◇P", _MODAL),
    "Always": ("Ⓖ P", _MODAL),
    "Eventually": ("Ⓕ P", _MODAL),
    "Next": ("Ⓝ P", _MODAL),
    "Obligatory": ("Ⓞ P", _MODAL),
    "Permitted": ("Ⓟ P", _MODAL),
    "Knows": ("K_alice P", _MODAL),
    "Believes": ("B_bob P", _MODAL),
    "Says": ("Say_alice P", _MODAL),
    "Wants": ("Want_bob P", _MODAL),
    "Until": ("P Ⓤ Q", _MODAL),
    "Historically": ("⒣P", _MODAL),
    "Once": ("⒫P", _MODAL),
    "Previous": ("⒴P", _MODAL),
    "Since": ("P ⒮ Q", _MODAL),
    "Would": ("P □→ Q", _MODAL),
    "Might": ("P ◇→ Q", _MODAL),
    # Łukasiewicz (fl mode: unsorted + fuzzy).
    "LukNegation": ("¬P", _FL),
    "LukImplication": ("P → Q", _FL),
    "LukEquivalence": ("P ↔ Q", _FL),
    "WeakConjunction": ("P ∧ Q", _FL),
    "WeakDisjunction": ("P ∨ Q", _FL),
    "StrongConjunction": ("P ⊗ Q", _FL),
    "StrongDisjunction": ("P ⊕ Q", _FL),
    # Intuitionistic linear logic (linear mode only).
    "Tensor": ("A ⊗ B", _LIN),
    "With": ("A & B", _LIN),
    "OPlus": ("A ⊕ B", _LIN),
    "LinearImplies": ("A ⊸ B", _LIN),
    "OfCourse": ("!A", _LIN),
    # Lambek calculus (lambek mode only).
    "Product": ("A • B", _LAM),
    "Under": ("A \\ B", _LAM),
    "Over": ("B / A", _LAM),
}


def test_battery_covers_every_registered_operator():
    """Every OperatorSpec in OPERATORS has a round-trip battery entry.

    This is the completeness pin: a new ``register_operator(...)`` call
    without a matching ``_OPERATOR_BATTERY`` entry fails HERE, not silently.
    """
    missing = set(OPERATORS) - set(_OPERATOR_BATTERY)
    assert not missing, (
        f"Operator(s) {sorted(missing)} are registered in OPERATORS but have "
        "no tests/test_latex_roundtrip.py battery entry — add a "
        "representative formula for each."
    )
    # The converse also holds: no stale entries for operators no longer
    # registered (would indicate a rename/removal the battery didn't follow).
    stale = set(_OPERATOR_BATTERY) - set(OPERATORS)
    assert not stale, f"Stale battery entries for unregistered operators: {sorted(stale)}"


@pytest.mark.parametrize(
    "name, source, mode",
    [(name, source, mode) for name, (source, mode) in sorted(_OPERATOR_BATTERY.items())],
)
def test_operator_round_trip_latex(name, source, mode):
    """parse_latex(ast.to_latex(), <mode>) reproduces the AST for every registered operator."""
    ast = MSFLParser(**mode).parse(source)
    latex = ast.to_latex()
    back = parse_latex(latex, **mode)
    assert back == ast, (
        f"round-trip mismatch for operator {name!r}, source {source!r}\n"
        f"  latex   = {latex!r}\n"
        f"  unicode = {latex_to_unicode(latex)!r}\n"
        f"  back    = {back!r}"
    )


# ---------------------------------------------------------------------------
# Tier 2 — non-registry constructs: binders/terms with their own explicit
# _uni / _latex branch (Count, Cardinality, Measure, Nominal, Dependence,
# SlashedExists, One, Lambda, Application, and the three quantifier flavours).
# ---------------------------------------------------------------------------

_NON_REGISTRY_BATTERY = [
    ("Quantifier", "∀x P(x)", _FOL),
    ("Quantifier-exists", "∃x P(x)", _FOL),
    ("SortedQuantifier", "∀x:Human P(x)", _MSFOL),
    ("SecondOrderQuantifier", "∀P P(x)", _SO),
    ("Count-ge", "∃≥3 x P(x)", _FOL),
    ("Count-le", "∃≤3 x P(x)", _FOL),
    ("Count-eq", "∃=3 x P(x)", _FOL),
    ("SortedCount", "∃≥3 x:Nat P(x)", _MSFOL),
    ("Cardinality", "P(|{v : Votes(v)}|)", _FOL),
    ("SortedCardinality", "P(|{v:Human : Votes(v)}|)", _MSFOL),
    ("Measure", "μ(x, height) > μ(y, height)", _FOL),
    ("Nominal", "i", _MODAL),
    ("Nominal-in-context", "P ∧ i", _MODAL),
    ("Dependence-binary", "=(x, y)", _DEP),
    ("Dependence-constancy", "=(x)", _DEP),
    ("SlashedExists", "∃x/{y, z} R(x, y, z)", _DEP),
    ("One", "𝟙", _LIN),
    ("Lambda", "λx. P(x)", _FOL),
    ("Application", "(λx. P(x))(a)", _FOL),
]


@pytest.mark.parametrize("label, source, mode", _NON_REGISTRY_BATTERY)
def test_non_registry_construct_round_trip_latex(label, source, mode):
    """parse_latex(ast.to_latex(), <mode>) reproduces the AST for every non-registry construct."""
    ast = MSFLParser(**mode).parse(source)
    latex = ast.to_latex()
    back = parse_latex(latex, **mode)
    assert back == ast, (
        f"round-trip mismatch for {label!r}, source {source!r}\n"
        f"  latex   = {latex!r}\n"
        f"  unicode = {latex_to_unicode(latex)!r}\n"
        f"  back    = {back!r}"
    )


# ---------------------------------------------------------------------------
# Tier 3 — the single-letter (VARIABLE-headed) function-call grammar fix.
# ---------------------------------------------------------------------------
#
# Before the fix, Function('f', [...]).to_unicode_str() printed 'f(x)', which
# then FAILED to re-parse: the grammar's shared atom_term rule only let a
# >=2-letter NAME head a function call ('f' lexes as VARIABLE, and
# '?atom_term: VARIABLE' has no continuation into "("), producing
# "SYNTAX_ERROR: Invalid variable 'f' - unexpected character '(' ...". See
# msflparser.py's _allow_single_letter_function_calls / LambdaTransformer.function_.

class TestSingleLetterFunctionRoundTrip:

    def test_unicode_round_trip_in_atom_position(self):
        # f(x) as a predicate argument — the originally-reported failure shape.
        atom = Atom("P", [Function("f", [Variable("x")])])
        text = atom.to_unicode_str()
        assert text == "P(f(x))"
        assert MSFLParser().parse(text) == atom

    def test_unicode_round_trip_in_comparison_position(self):
        # f(x) = y — a single-letter function head in an infix comparison.
        eq = Atom("=", [Function("f", [Variable("x")]), Variable("y")])
        text = eq.to_unicode_str()
        assert text == "f(x) = y"
        assert MSFLParser().parse(text) == eq

    def test_latex_round_trip(self):
        atom = Atom("P", [Function("f", [Variable("x")])])
        latex = atom.to_latex()
        assert parse_latex(latex) == atom

    def test_nested_single_letter_functions(self):
        # f(g(x)) — both heads are single letters, nested.
        inner = Function("g", [Variable("x")])
        outer = Function("f", [inner])
        atom = Atom("P", [outer])
        text = atom.to_unicode_str()
        assert text == "P(f(g(x)))"
        assert MSFLParser().parse(text) == atom

    def test_two_letter_arity_two(self):
        # Multi-argument single-letter function, arity 2.
        atom = Atom("P", [Function("f", [Variable("x"), Variable("y")])])
        text = atom.to_unicode_str()
        assert text == "P(f(x, y))"
        assert MSFLParser().parse(text) == atom

    def test_bare_single_letter_still_a_variable_when_not_applied(self):
        # Regression guard: a lone single letter NOT followed by "(" must
        # still parse as a Variable, exactly as before the grammar patch.
        assert MSFLParser().parse("P(a)") == Atom("P", [Variable("a")])

    def test_lambda_application_arg_still_a_variable(self):
        # (λx. P(x))(a): 'a' is a bare application argument, not followed by
        # "(" — must still read as Variable("a"), not be affected by the
        # VARIABLE "(" termlist ")" alternative (test_msfl_parser.py pins the
        # same fact directly against MSFLParser; repeated here as a guard
        # specific to the grammar patch in this module).
        from unicode_fol_kit.fol.nodes import Application, Lambda, LambdaVar
        result = MSFLParser().parse("(λx. P(x))(a)")
        assert isinstance(result, Application)
        assert result.func == Lambda(LambdaVar("x"), Atom("P", [LambdaVar("x")]))
        assert result.arg == Variable("a")
