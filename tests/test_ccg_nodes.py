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
    SortedCount, SortedCardinality,
    Number, Variable, Constant, Atom, And, Or, Not, Implies, Iff, Quantifier,
)

_FOL = MSFLParser()
_MODAL = MSFLParser(modal=True)
_MSFOL = MSFLParser(many_sorted=True)
_SO = MSFLParser(second_order=True)


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
# Modal mode also accepts the NL / CCG translation-target nodes
#
# A CCG-derived logical form routinely nests a fol-only construct (Count / Measure /
# Cardinality / Contrast) UNDER a modal operator. These constructs must therefore be
# parseable in modal mode too, so the whole mixed formula round-trips as ONE string —
# not only as a hand-assembled AST. (Regression for the parser-mode-separation gap.)
# ===========================================================================

# Each string mixes a modal operator with a construct that used to be fol-only.
_MIXED_MODAL_CASES = [
    "B_a ∃≥3 x Pass(x)",              # the motivating case: Believes over 'at least 3'
    "K_a ∃=2 x Student(x)",          # Knows over 'exactly 2'
    "□∃≤5 x P(x)",                   # box over 'at most 5'
    "◇∃≥1 x Q(x)",                   # diamond over 'at least 1'
    "Say_a ∃≥3 x P(x)",              # Says over a count
    "Want_a ∃=1 x Win(x)",           # Wants over 'exactly 1'
    "P(a) Ⓒ ◇Q(b)",                 # Contrast with a modal operand
    "μ(a, height) > μ(b, height)",   # Measure term in modal mode
    "|{x : P(x)}| > |{x : Q(x)}|",   # Cardinality term in modal mode
    "B_a (|{x : Passed(x)}| > n)",   # Believes over a cardinality comparison
    "K_a (P(a) Ⓒ Q(b))",            # Knows over a Contrast
    "□(∃≥2 x P(x)) → ◇(∃≥2 x P(x))", # counts nested under two modalities in one formula
]


@pytest.mark.parametrize("text", _MIXED_MODAL_CASES)
def test_modal_mode_accepts_nl_nodes_and_round_trips(text):
    # Parses in modal mode and round-trips as a single string (item #1).
    _rt(_MODAL, _MODAL.parse(text))


def test_modal_count_matches_hand_built_ast():
    # The parsed modal string is exactly the AST one would build by hand — i.e.
    # modal-mode Count is the SAME node as fol-mode Count, not a look-alike.
    from unicode_fol_kit.fol.nodes import Believes
    parsed = _MODAL.parse("B_a ∃≥3 x Pass(x)")
    hand = Believes(Constant("a"),
                    Count("ge", Number(3), Variable("x"), Atom("Pass", [Variable("x")])))
    assert parsed == hand


def test_fol_count_and_modal_count_are_identical_nodes():
    # Same counting formula, parsed in each mode, yields byte-identical ASTs.
    assert _FOL.parse("∃≥3 x P(x)") == _MODAL.parse("∃≥3 x P(x)")
    assert _FOL.parse("P Ⓒ Q") == _MODAL.parse("P Ⓒ Q")
    assert _FOL.parse("|{x : P(x)}| > c") == _MODAL.parse("|{x : P(x)}| > c")
    assert _FOL.parse("μ(a, b) > c") == _MODAL.parse("μ(a, b) > c")


# ===========================================================================
# Canonical form / exact_match alpha-normalises the Count and Cardinality binders
#
# Count and Cardinality bind a Variable over their matrix, exactly like a quantifier,
# so two forms that differ ONLY in the bound-variable name must be canonically equal
# (and exact_match up to canonical form). Distinct op / bound n / matrix must NOT
# collapse. (Regression for the alpha-equivalence gap — item #2.)
# ===========================================================================

def test_count_alpha_equivalent_exact_match():
    from unicode_fol_kit import exact_match
    a = _FOL.parse("∃≥3 x P(x)")
    b = _FOL.parse("∃≥3 y P(y)")
    assert a != b                      # structurally distinct (different bound name)
    assert exact_match(a, b)           # …but alpha-equivalent


def test_cardinality_alpha_equivalent_exact_match():
    from unicode_fol_kit import exact_match
    a = _FOL.parse("|{x : Votes(x)}| > c")
    b = _FOL.parse("|{y : Votes(y)}| > c")
    assert a != b
    assert exact_match(a, b)


def test_count_canonical_invariants():
    from unicode_fol_kit import canonicalize
    a = _FOL.parse("∃=2 x (P(x) ∧ Q(x))")
    b = _FOL.parse("∃=2 w (Q(w) ∧ P(w))")   # alpha-renamed AND commuted matrix
    ca, cb = canonicalize(a), canonicalize(b)
    assert ca == cb                          # P3 alpha + P4 comm
    assert canonicalize(ca) == ca            # P2 idempotent


def test_count_op_and_bound_are_not_alpha_collapsed():
    from unicode_fol_kit import exact_match
    base = _FOL.parse("∃≥3 x P(x)")
    assert not exact_match(base, _FOL.parse("∃≥5 x P(x)"))   # different bound n
    assert not exact_match(base, _FOL.parse("∃≤3 x P(x)"))   # different op
    assert not exact_match(base, _FOL.parse("∃=3 x P(x)"))   # different op


def test_count_dedup_under_idempotent_conjunction():
    # ∃≥3 x P(x) ∧ ∃≥3 y P(y) are alpha-equal operands of an idempotent ∧, so they
    # collapse to a single conjunct; a genuinely different count must survive.
    from unicode_fol_kit import canonicalize
    same = _FOL.parse("∃≥3 x P(x) ∧ ∃≥3 y P(y)")
    assert canonicalize(same) == canonicalize(_FOL.parse("∃≥3 x P(x)"))
    diff = _FOL.parse("∃≥3 x P(x) ∧ ∃≥5 y P(y)")
    assert canonicalize(diff) != canonicalize(_FOL.parse("∃≥3 x P(x)"))


def test_count_free_agent_capture_not_conflated():
    # Alpha-normalisation must stay capture-safe: a count binding x with a free x
    # inside must not be conflated with one where that x is genuinely free elsewhere.
    from unicode_fol_kit import exact_match
    a = _FOL.parse("∃≥2 x R(x, y)")   # y free
    b = _FOL.parse("∃≥2 z R(z, y)")   # y still free -> equal
    c = _FOL.parse("∃≥2 x R(x, w)")   # w free, different name -> NOT equal
    assert exact_match(a, b)
    assert not exact_match(a, c)


# ===========================================================================
# MSFOL (classical many-sorted) — full sorted parity
#
# The counting quantifier and set-cardinality binders take sort annotations in MSFOL
# (SortedCount ∃≥n x:S φ, SortedCardinality |{v:S : φ}|); the non-binders Contrast, Xor,
# and the Measure term drop in unchanged. Sorted counting reduces to plain FOL by
# guarding the matrix with the sort predicate and reusing Count's distinct-witnesses
# encoding, so its logic is checkable with Z3.
# ===========================================================================

_MSFOL_CASES = [
    "∃≥3 x:Student Pass(x)",
    "∃=2 x:Human Tall(x)",
    "∃≤5 x:Cat Sleeps(x)",
    "∀x:Human ∃≥2 y:Dog Owns(x, y)",            # sorted count under a sorted ∀
    "|{x:Student : Pass(x)}| > z",              # sorted cardinality
    "|{x:Student : Pass(x)}| > |{x:Student : Fail(x)}|",
    "P(a) Ⓒ Q(b)",                              # Contrast in MSFOL
    "R ⊕ S",                                    # Xor in MSFOL
    "μ(x, y) > μ(u, v)",                        # Measure term in MSFOL
    "∃=1 x:S (P(x) Ⓒ Q(x))",                    # count over a Contrast matrix
]


@pytest.mark.parametrize("text", _MSFOL_CASES)
def test_msfol_sorted_parity_round_trips(text):
    _rt(_MSFOL, _MSFOL.parse(text))


def test_sorted_count_structure_and_hand_ast():
    s = _MSFOL.parse("∃≥3 x:Student Pass(x)")
    assert isinstance(s, SortedCount)
    assert s.op == "ge" and s.n == Number(3) and s.sort == "Student"
    assert s == SortedCount("ge", Number(3), Variable("x"), "Student",
                            Atom("Pass", [Variable("x")]))


def test_sorted_cardinality_structure():
    c = _MSFOL.parse("|{x:Student : Pass(x)}| > z").args[0]
    assert isinstance(c, SortedCardinality)
    assert c.variable == Variable("x") and c.sort == "Student"


def test_sorted_count_binds_its_variable():
    s = _MSFOL.parse("∃≥2 x:S R(x, y)")
    assert free_variables(s) == {Variable("y")}   # x is bound, y free


def test_sorted_count_reduces_and_z3_agrees():
    # Sorted counting is FOL-expressible (sort-guarded distinct witnesses); Z3 checks it.
    assert is_valid(_MSFOL.parse("∃≥2 x:S P(x) → ∃≥1 x:S P(x)"))
    assert not is_valid(_MSFOL.parse("∃≥1 x:S P(x) → ∃≥2 x:S P(x)"))
    assert is_valid(_MSFOL.parse("∃=2 x:S P(x) → ∃≥2 x:S P(x)"))
    assert is_satisfiable(_MSFOL.parse("∃=2 x:S P(x)"))
    assert is_valid(_MSFOL.parse("∃≥0 x:S P(x)"))     # vacuously true on non-empty domain


def test_sorted_count_sort_guard_is_inside_the_count():
    from unicode_fol_kit import to_fol
    reduced = to_fol(_MSFOL.parse("∃≥1 x:S P(x)")).to_unicode_str()
    assert reduced == "∃≥1 x (S(x) ∧ P(x))"


def test_sorted_cardinality_has_no_first_order_export():
    card = _MSFOL.parse("|{x:S : P(x)}| > z")
    for export in (card.to_z3, card.to_prover9, card.to_tptp):
        with pytest.raises(NotImplementedError):
            export()


def test_sorted_count_alpha_equivalence_and_significance():
    from unicode_fol_kit import exact_match
    assert exact_match(_MSFOL.parse("∃≥3 x:S P(x)"), _MSFOL.parse("∃≥3 y:S P(y)"))
    assert not exact_match(_MSFOL.parse("∃≥3 x:S P(x)"), _MSFOL.parse("∃≥3 x:T P(x)"))  # sort
    assert not exact_match(_MSFOL.parse("∃≥3 x:S P(x)"), _MSFOL.parse("∃≤3 x:S P(x)"))  # op
    assert not exact_match(_MSFOL.parse("∃≥3 x:S P(x)"), _MSFOL.parse("∃≥4 x:S P(x)"))  # n
    assert exact_match(_MSFOL.parse("|{x:S : P(x)}| > z"),
                       _MSFOL.parse("|{y:S : P(y)}| > z"))
    # a sorted count is NOT the same canonical shape as the unsorted one
    assert not exact_match(_MSFOL.parse("∃≥3 x:S P(x)"), _FOL.parse("∃≥3 x P(x)"))


def test_sorted_verbalization():
    assert (to_english(_MSFOL.parse("∃≥3 x:Student Pass(x)"))
            == "there are at least 3 x of sort Student such that x is pass")
    assert "the number of x of sort Student such that" in \
        to_english(_MSFOL.parse("|{x:Student : Pass(x)}| > z"))


def test_msfol_still_requires_sorts_on_plain_quantifiers():
    # The parity additions must not loosen MSFOL's sort discipline: an UNsorted count
    # (no ':Sort') is rejected in MSFOL, exactly like an unsorted ∀/∃.
    from unicode_fol_kit import NamingError, ParsingError
    with pytest.raises((NamingError, ParsingError)):
        _MSFOL.parse("∃≥3 x P(x)")


def test_second_order_parity_round_trips():
    for text in ("∃≥3 x P(x)", "∃P ∃≥2 x P(x)", "∀P (∃=1 x P(x) → Q(x))",
                 "P(a) Ⓒ Q(b)", "∃P (|{x : P(x)}| > z)", "μ(a, b) > z"):
        _rt(_SO, _SO.parse(text))


# ===========================================================================
# Public API surface
# ===========================================================================

def test_new_nodes_exported():
    import unicode_fol_kit as u
    for name in ("Count", "Measure", "Cardinality", "Contrast", "Says", "Wants",
                 "SortedCount", "SortedCardinality",
                 "parse_prover9_problem", "load_prover9", "Prover9Formula"):
        assert hasattr(u, name) and name in u.__all__, name
