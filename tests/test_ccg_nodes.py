"""Tests for the CCG-front-end node extensions: the assertive / bouletic attitude
operators (Says / Wants), the counting quantifier (Count: ∃≥n / ∃≤n / ∃=n), the
degree term (Measure: μ), the set-cardinality term (Cardinality: |{v : φ}|), and the
concessive connective (Contrast: Ⓒ).

The primary oracle for the FOL-expressible constructs (Count, Contrast) is logical:
the standard-translation / truth-functional reading is checked with the Z3 backend
(``is_valid`` / ``is_satisfiable``). Round-trip (``parse(node.to_unicode_str()) == node``
and ``Node.from_dict(node.to_dict()) == node``) is checked for every node, and the
attitude operators are additionally checked against the Kripke evaluator and the modal
tableau (non-factive Says, non-veridical Wants, K-distribution valid).
"""

import pytest

from unicode_fol_kit import (
    MSFLParser, Node, is_valid, is_satisfiable, free_variables, substitute,
    KripkeModel, satisfies_modal, is_modal_valid, to_english,
)
from unicode_fol_kit.fol.nodes import (
    Count, Measure, Cardinality, Contrast, Says, Wants,
    Number, Variable, Constant, Atom, And, Or, Not, Implies, Iff, Quantifier,
)

_FOL = MSFLParser()
_MODAL = MSFLParser(modal=True)


def _rt(parser, node):
    """Assert a node round-trips through both Unicode and dict serialisation."""
    assert parser.parse(node.to_unicode_str()) == node, node.to_unicode_str()
    assert Node.from_dict(node.to_dict()) == node, node.to_dict()


# ===========================================================================
# Says / Wants — assertive (non-factive) and bouletic (non-veridical) operators
# ===========================================================================

def test_says_wants_parse_and_structure():
    s = _MODAL.parse("Say_alice Rain")
    assert isinstance(s, Says)
    assert s.agent == Constant("alice") and s.formula == Atom("Rain", [])
    w = _MODAL.parse("Want_bob Win(bob)")
    assert isinstance(w, Wants)
    assert w.agent == Constant("bob")


def test_says_wants_round_trip():
    for text in ("Say_alice P", "Want_bob Q(b)", "Say_a (P → Q)",
                 "Say_alice P ∧ Want_bob Q", "¬Say_a P"):
        _rt(_MODAL, _MODAL.parse(text))


def test_says_bound_agent_vs_free_agent():
    # A free agent is demoted to a named Constant…
    free = _MODAL.parse("Say_alice P")
    assert isinstance(free.agent, Constant)
    # …but an agent bound by an enclosing quantifier stays a Variable.
    bound = _MODAL.parse("∀x (Speaker(x) → Say_x P(x))")
    inner = bound.formula.right  # Says(...)
    assert isinstance(inner, Says) and isinstance(inner.agent, Variable)
    assert inner.agent.name == "x"
    _rt(_MODAL, bound)


def test_says_legacy_string_agent_coerced():
    assert Says("alice", Atom("P", [])).agent == Constant("alice")
    assert Wants("bob", Atom("Q", [])).agent == Constant("bob")


def test_says_non_factive_wants_non_veridical():
    # Say_a P ⊭ P (an assertion need not be true); likewise Want_a P ⊭ P.
    assert not is_modal_valid(_MODAL.parse("(Say_a P) → P"))
    assert not is_modal_valid(_MODAL.parse("(Want_a P) → P"))
    # …and Says is not doxastic: Say_a P ⊭ B_a P.
    assert not is_modal_valid(_MODAL.parse("(Say_a P) → (B_a P)"))


def test_says_wants_are_normal_modalities_k_distribution():
    # K (distribution) holds — both are normal modal operators.
    assert is_modal_valid(_MODAL.parse("(Say_a (P → Q)) → ((Say_a P) → (Say_a Q))"))
    assert is_modal_valid(_MODAL.parse("(Want_a (P → Q)) → ((Want_a P) → (Want_a Q))"))


def test_says_kripke_eval():
    # Say_a P true at 0 iff P holds at every "Say:a"-successor of 0.
    say_p = _MODAL.parse("Say_a P")
    holds = KripkeModel({0, 1}, {"Say:a": {(0, 1)}}, {1: {"P"}})
    fails = KripkeModel({0, 1}, {"Say:a": {(0, 1)}}, {1: set()})
    assert satisfies_modal(say_p, holds, 0) is True
    assert satisfies_modal(say_p, fails, 0) is False


def test_says_wants_reject_classical_export():
    for node in (_MODAL.parse("Say_a P"), _MODAL.parse("Want_a P")):
        with pytest.raises(NotImplementedError):
            node.to_z3()
        with pytest.raises(NotImplementedError):
            node.to_tptp()
        with pytest.raises(NotImplementedError):
            node.to_prover9()


def test_says_distinct_from_knows_believes():
    p = Atom("P", [])
    assert Says("a", p) != Knows_node("a", p)
    assert Wants("a", p) != Says("a", p)


def Knows_node(agent, formula):
    """Local Knows constructor (kept out of the module import list for clarity)."""
    from unicode_fol_kit.fol.nodes import Knows
    return Knows(agent, formula)


# ===========================================================================
# Count — counting quantifier ∃≥n / ∃≤n / ∃=n (symbolic n)
# ===========================================================================

def test_count_parse_all_ops():
    ge = _FOL.parse("∃≥3 x (R(x) ∧ Q(x))")
    le = _FOL.parse("∃≤2 y P(y)")
    eq = _FOL.parse("∃=4 z S(z)")
    assert isinstance(ge, Count) and ge.op == "ge" and ge.n == Number(3)
    assert le.op == "le" and le.n == Number(2)
    assert eq.op == "eq" and eq.n == Number(4)
    assert ge.variable == Variable("x")


def test_count_round_trip():
    for text in ("∃≥3 x (R(x) ∧ Q(x))", "∃≤2 y P(y)", "∃=4 z S(z)",
                 "∃≥1 x P(x)", "∃=0 x P(x)"):
        _rt(_FOL, _FOL.parse(text))


def test_count_keeps_n_symbolic_no_clamp():
    # The whole point: an arbitrarily large bound is NOT clamped to plain ∃.
    big = _FOL.parse("∃≥500 x P(x)")
    assert isinstance(big, Count) and big.n == Number(500)
    _rt(_FOL, big)
    # Coordinated per-noun counts compose as a conjunction of Counts.
    coord = _FOL.parse("(∃≥4 x Bedroom(x)) ∧ (∃≥2 y Bath(y))")
    assert isinstance(coord, And)
    assert isinstance(coord.left, Count) and coord.left.n == Number(4)
    assert isinstance(coord.right, Count) and coord.right.n == Number(2)


def test_count_rejects_non_integer_bound():
    from unicode_fol_kit import ParsingError
    with pytest.raises((ValueError, ParsingError, Exception)):
        _FOL.parse("∃≥3.5 x P(x)")
    with pytest.raises(ValueError):
        Count("ge", Number(2.5), Variable("x"), Atom("P", [Variable("x")]))
    with pytest.raises(ValueError):
        Count("bogus", Number(1), Variable("x"), Atom("P", [Variable("x")]))


def test_count_binds_its_variable_free_variables():
    # x is bound by the count; y is free in the matrix.
    c = _FOL.parse("∃≥3 x R(x, y)")
    assert {v.name for v in free_variables(c)} == {"y"}


def test_count_substitution_is_capture_avoiding():
    c = _FOL.parse("∃≥3 x R(x, y)")
    sub = substitute(c, Variable("y"), Constant("bob"))
    assert isinstance(sub, Count) and sub.op == "ge" and sub.n == Number(3)
    assert sub == _FOL.parse("∃≥3 x R(x, bob)")
    assert free_variables(sub) == set()
    # Substituting the bound variable's name is a no-op inside (shadowed).
    sub2 = substitute(c, Variable("x"), Constant("a"))
    assert sub2 == c


def test_count_semantics_via_z3():
    # ∃≥1 x P(x)  ≡  ∃x P(x)
    assert is_valid(Iff(_FOL.parse("∃≥1 x P(x)"), _FOL.parse("∃x P(x)")))
    # ∃≤0 x P(x)  ≡  ∃=0 x P(x)  ≡  ¬∃x P(x)
    none = _FOL.parse("¬∃x P(x)")
    assert is_valid(Iff(_FOL.parse("∃≤0 x P(x)"), none))
    assert is_valid(Iff(_FOL.parse("∃=0 x P(x)"), none))
    # monotonicity: ∃≥2 → ∃≥1 (valid); converse not valid.
    assert is_valid(Implies(_FOL.parse("∃≥2 x P(x)"), _FOL.parse("∃≥1 x P(x)")))
    assert not is_valid(Implies(_FOL.parse("∃≥1 x P(x)"), _FOL.parse("∃≥2 x P(x)")))
    # ∃=1 x P(x)  ≡  the classic "exactly one" formula.
    exactly_one = _FOL.parse("∃x (P(x) ∧ ∀y (P(y) → x = y))")
    assert is_valid(Iff(_FOL.parse("∃=1 x P(x)"), exactly_one))
    # at most 1 and at least 2 is contradictory.
    assert not is_satisfiable(And(_FOL.parse("∃≤1 x P(x)"), _FOL.parse("∃≥2 x P(x)")))
    # eq is ge ∧ le.
    assert is_valid(Iff(_FOL.parse("∃=2 x P(x)"),
                        And(_FOL.parse("∃≥2 x P(x)"), _FOL.parse("∃≤2 x P(x)"))))


def test_count_exports_do_not_crash():
    c = _FOL.parse("∃≥2 x (P(x) ∧ Q(x))")
    assert "?" in c.to_tptp()          # existential expansion uses ?[X]
    assert "exists" in c.to_prover9()  # Prover9 existential
    c.to_z3()  # must not raise


def test_count_export_large_n_balanced_and_bounded():
    # The conjunction is built as a balanced tree, so a moderately large n exports
    # without overflowing Python's recursion limit (regression: used to RecursionError
    # at n>=44 with a left-associative chain).
    for n in (50, 200, 500):
        _FOL.parse(f"∃≥{n} x P(x)").to_z3()
        _FOL.parse(f"∃≤{n} x P(x)").to_tptp()   # ∃≤n needs n+1 witnesses; bound is on n
        _FOL.parse(f"∃={n} x P(x)").to_prover9()
    # Beyond the expansion bound the exporters raise a CLEAR error (not RecursionError).
    for op in ("∃≥", "∃≤", "∃="):
        with pytest.raises(NotImplementedError):
            _FOL.parse(f"{op}600 x P(x)").to_z3()
    # …but the node stays symbolic and round-trips for any n (no clamping).
    huge = _FOL.parse("∃≥1000000 x P(x)")
    assert huge.n == Number(1000000)
    _rt(_FOL, huge)


# ===========================================================================
# Measure — degree term μ(entity, dimension)
# ===========================================================================

def test_measure_parse_and_round_trip():
    cmp = _FOL.parse("μ(x, height) > μ(y, height)")
    assert isinstance(cmp, Atom) and cmp.predicate == ">"
    left = cmp.args[0]
    assert isinstance(left, Measure)
    assert left.entity == Variable("x") and left.dimension == Constant("height")
    _rt(_FOL, cmp)


def test_measure_as_predicate_argument():
    f = _FOL.parse("Tall(μ(alice, height))")
    assert isinstance(f.args[0], Measure)
    _rt(_FOL, f)


def test_measure_arity_must_be_two():
    with pytest.raises(Exception):
        _FOL.parse("μ(x)")
    with pytest.raises(Exception):
        _FOL.parse("μ(x, y, z)")


def test_measure_export_is_uninterpreted_function():
    cmp = _FOL.parse("μ(x, height) > μ(y, height)")
    # exports as an uninterpreted binary function named "measure"
    assert "measure(" in cmp.to_prover9()
    assert "measure(" in cmp.to_tptp()
    cmp.to_z3()  # must not raise
    # the comparison is contingently satisfiable (> is uninterpreted here)
    assert is_satisfiable(cmp)


# ===========================================================================
# Cardinality — set-cardinality term |{v : φ}|
# ===========================================================================

def test_cardinality_parse_and_round_trip():
    cmp = _FOL.parse("|{v : Votes(x, v)}| > |{v : Votes(y, v)}|")
    assert isinstance(cmp, Atom) and cmp.predicate == ">"
    left = cmp.args[0]
    assert isinstance(left, Cardinality)
    assert left.variable == Variable("v")
    assert left.formula == Atom("Votes", [Variable("x"), Variable("v")])
    _rt(_FOL, cmp)


def test_cardinality_binds_its_variable():
    # v is bound by the cardinality; x and c are free.
    f = _FOL.parse("|{v : R(x, v)}| > c")
    assert {var.name for var in free_variables(f)} == {"x", "c"}
    sub = substitute(f, Variable("x"), Constant("bob"))
    assert sub == _FOL.parse("|{v : R(bob, v)}| > c")


def test_cardinality_inner_formula_is_a_subformula():
    f = _FOL.parse("|{v : R(v) ∧ S(v)}| > c")
    card = f.args[0]
    # the matrix renders at the full formula level inside the braces
    assert isinstance(card, Cardinality) and isinstance(card.formula, And)
    _rt(_FOL, f)


def test_cardinality_has_no_first_order_export():
    card = _FOL.parse("|{v : P(v)}| > c").args[0]
    with pytest.raises(NotImplementedError):
        card.to_z3()
    with pytest.raises(NotImplementedError):
        card.to_prover9()
    with pytest.raises(NotImplementedError):
        card.to_tptp()


# ===========================================================================
# Contrast — concessive connective (truth-functionally ∧)
# ===========================================================================

def test_contrast_parse_and_round_trip():
    c = _FOL.parse("P(alice) Ⓒ Q(bob)")
    assert isinstance(c, Contrast)
    assert c.left == Atom("P", [Constant("alice")])
    assert c.right == Atom("Q", [Constant("bob")])
    _rt(_FOL, c)


def test_contrast_is_truth_functionally_conjunction():
    assert is_valid(Iff(_FOL.parse("P Ⓒ Q"), _FOL.parse("P ∧ Q")))
    # exports behave exactly like And
    assert _FOL.parse("P Ⓒ Q").to_tptp() == _FOL.parse("P ∧ Q").to_tptp()
    assert _FOL.parse("P Ⓒ Q").to_prover9() == _FOL.parse("P ∧ Q").to_prover9()


def test_contrast_does_not_mix_with_conjunction_without_parens():
    # Same no-mixing rule as ∧/∨/⊕ — surfaces as a lexer- or parser-level error.
    from unicode_fol_kit import NamingError, ParsingError
    with pytest.raises((NamingError, ParsingError)):
        _FOL.parse("P Ⓒ Q ∧ R")
    # …but parenthesised mixing is fine and round-trips.
    _rt(_FOL, _FOL.parse("(P Ⓒ Q) ∧ R"))


# ===========================================================================
# Verbalization (best-effort English; not a parse inverse)
# ===========================================================================

def test_verbalize_new_nodes():
    assert to_english(_FOL.parse("∃≥2 x Dog(x)")).startswith("there are at least 2 x")
    assert to_english(_FOL.parse("∃≤1 x Dog(x)")).startswith("there are at most 1 x")
    assert to_english(_FOL.parse("∃=3 x Dog(x)")).startswith("there are exactly 3 x")
    assert "says that" in to_english(_MODAL.parse("Say_alice Rain"))
    assert "wants it to be that" in to_english(_MODAL.parse("Want_bob Win"))
    assert "whereas" in to_english(_FOL.parse("P Ⓒ Q"))
    assert to_english(_FOL.parse("μ(x, height) > c")).startswith("the height of x")
    assert "the number of v such that" in to_english(_FOL.parse("|{v : P(v)}| > c"))


# ===========================================================================
# Public API surface
# ===========================================================================

def test_new_nodes_exported():
    import unicode_fol_kit as u
    for name in ("Count", "Measure", "Cardinality", "Contrast", "Says", "Wants",
                 "parse_prover9_problem", "load_prover9", "Prover9Formula"):
        assert hasattr(u, name) and name in u.__all__, name
