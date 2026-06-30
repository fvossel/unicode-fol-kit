"""Tests for the reverse importers: TPTP, Prover9, and Z3 (expr + SMT-LIB2).

The primary oracle is **round-trip**: for the syntactic importers (TPTP, Prover9)
``parse(node.to_X()) == node`` over random formulas; for the Z3 importer (which
collapses variables/constants/numbers onto one uninterpreted sort and may normalise)
the oracle is **logical equivalence** ``is_valid(Iff(node, from_z3(node.to_z3())))``,
with structural spot-checks for the cases Z3 does preserve.
"""

import random

import pytest
import z3

from unicode_fol_kit import is_valid
from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable, Constant, Number, Function,
)
from unicode_fol_kit import (
    parse_tptp, parse_tptp_formula, load_tptp, TptpFormula,
    parse_prover9, from_z3, parse_smtlib, load_smtlib,
)
from unicode_fol_kit.fol.tptp_input import TptpParsingError
from unicode_fol_kit.fol.prover9_input import Prover9ParsingError


# ---------------------------------------------------------------------------
# Random formula generators (toolkit naming conventions)
# ---------------------------------------------------------------------------

_PREDS = [("P", 1), ("Q", 1), ("R", 2), ("Loves", 2), ("Big", 0)]
_CONSTS = ["a", "b", "c", "alice"]
_FUNCS = [("f", 1), ("g", 2), ("succ", 1)]
_VARS = ["x", "y", "z", "w"]
_CMP = ["<", ">", "≤", "≥"]
_ARITH = ["+", "-", "*", "/"]


def _rand_term(rng, depth, scope):
    choices = ["const", "num"] + (["var"] if scope else []) + (["func", "arith"] if depth > 0 else [])
    kind = rng.choice(choices)
    if kind == "const":
        return Constant(rng.choice(_CONSTS))
    if kind == "num":
        return Number(rng.randint(0, 9))
    if kind == "var":
        return Variable(rng.choice(scope))
    if kind == "func":
        name, arity = rng.choice(_FUNCS)
        return Function(name, [_rand_term(rng, depth - 1, scope) for _ in range(arity)])
    op = rng.choice(_ARITH)
    return Function(op, [_rand_term(rng, depth - 1, scope), _rand_term(rng, depth - 1, scope)])


def _rand_atom(rng, scope, *, comparisons=True):
    roll = rng.random()
    if roll < 0.15:
        return Atom("=", [_rand_term(rng, 1, scope), _rand_term(rng, 1, scope)])
    if roll < 0.25:
        return Atom("≠", [_rand_term(rng, 1, scope), _rand_term(rng, 1, scope)])
    if comparisons and roll < 0.4:
        return Atom(rng.choice(_CMP), [_rand_term(rng, 1, scope), _rand_term(rng, 1, scope)])
    name, arity = rng.choice(_PREDS)
    return Atom(name, [_rand_term(rng, 1, scope) for _ in range(arity)])


def _rand_formula(rng, depth, scope, *, connectives, comparisons=True):
    if depth <= 0 or rng.random() < 0.4:
        return _rand_atom(rng, scope, comparisons=comparisons)
    kind = rng.choice(connectives + ["all", "ex"])
    if kind == "not":
        return Not(_rand_formula(rng, depth - 1, scope, connectives=connectives, comparisons=comparisons))
    if kind in ("all", "ex"):
        var = rng.choice(_VARS)
        qtype = "∀" if kind == "all" else "∃"
        return Quantifier(qtype, Variable(var),
                          _rand_formula(rng, depth - 1, scope + [var],
                                        connectives=connectives, comparisons=comparisons))
    cls = {"and": And, "or": Or, "xor": Xor, "imp": Implies, "iff": Iff}[kind]
    return cls(_rand_formula(rng, depth - 1, scope, connectives=connectives, comparisons=comparisons),
               _rand_formula(rng, depth - 1, scope, connectives=connectives, comparisons=comparisons))


# ---------------------------------------------------------------------------
# TPTP
# ---------------------------------------------------------------------------

def test_tptp_round_trip_random():
    rng = random.Random(20260627)
    conn = ["not", "and", "or", "xor", "imp", "iff"]
    for _ in range(1500):
        f = _rand_formula(rng, rng.randint(1, 4), [], connectives=conn)
        assert parse_tptp_formula(f.to_tptp()) == f, f.to_unicode_str()


def test_tptp_problem_file():
    text = """
    % Socrates is mortal
    fof(ax1, axiom, ![X]: (man(X) => mortal(X))).
    fof(ax2, hypothesis, man(socrates)).
    fof(goal, conjecture, mortal(socrates)).
    cnf(cl1, axiom, (~p(X) | q(X))).
    """
    result = parse_tptp(text)
    assert len(result) == 4
    assert all(isinstance(r, TptpFormula) for r in result)
    assert result[0].name == "ax1" and result[0].role == "axiom"
    assert result[1].formula == Atom("Man", [Constant("socrates")])
    assert result[2].role == "conjecture"
    assert result[3].formula == Or(Not(Atom("P", [Variable("x")])), Atom("Q", [Variable("x")]))


def test_tptp_equality_and_arithmetic():
    assert parse_tptp_formula("(a = b)") == Atom("=", [Constant("a"), Constant("b")])
    assert parse_tptp_formula("(a != b)") == Atom("≠", [Constant("a"), Constant("b")])
    assert parse_tptp_formula("$less(a, b)") == Atom("<", [Constant("a"), Constant("b")])
    assert parse_tptp_formula("$greatereq(a, b)") == Atom("≥", [Constant("a"), Constant("b")])
    assert parse_tptp_formula("p($sum(a, b))") == Atom("P", [Function("+", [Constant("a"), Constant("b")])])


def test_tptp_multi_variable_quantifier():
    # ![X,Y]: r(X,Y) nests to ∀x ∀y R(x,y)
    got = parse_tptp_formula("![X,Y]: r(X, Y)")
    expected = Quantifier("∀", Variable("x"),
                          Quantifier("∀", Variable("y"),
                                     Atom("R", [Variable("x"), Variable("y")])))
    assert got == expected


def test_tptp_reverse_implication():
    # a <= b  means  b => a
    assert parse_tptp_formula("(p(X) <= q(X))") == Implies(
        Atom("Q", [Variable("x")]), Atom("P", [Variable("x")]))


@pytest.mark.parametrize("bad", ["![X]: (p(X)", "p(X) &", "fluffle(x).", ")("])
def test_tptp_rejects_malformed(bad):
    with pytest.raises(TptpParsingError):
        parse_tptp_formula(bad)


def test_tptp_single_quoted_atoms():
    # TPTP single-quoted atoms (the form OWL->FOL dumps use for IRIs) are read as
    # functor / predicate / constant names with the quotes stripped.
    f = parse_tptp_formula("'http___ex_org_Thing'(X)")
    assert f == Atom("Http___ex_org_Thing", [Variable("x")])
    g = parse_tptp_formula("'rel'(X, 'indiv_1')")
    assert g == Atom("Rel", [Variable("x"), Constant("indiv_1")])
    # escaped quote inside a single-quoted atom is unescaped
    h = parse_tptp_formula(r"'a\'b'(x)")
    assert h.predicate == "A'b"


# ---------------------------------------------------------------------------
# Prover9
# ---------------------------------------------------------------------------

def test_prover9_round_trip_random():
    rng = random.Random(424242)
    # to_prover9 desugars Xor, so exclude it from the structural round-trip.
    conn = ["not", "and", "or", "imp", "iff"]
    for _ in range(1500):
        f = _rand_formula(rng, rng.randint(1, 4), [], connectives=conn)
        assert parse_prover9(f.to_prover9()) == f, f.to_unicode_str()


def test_prover9_curated():
    assert parse_prover9("(all X (man(X) -> mortal(X))).") == Quantifier(
        "∀", Variable("x"),
        Implies(Atom("man", [Variable("x")]), Atom("mortal", [Variable("x")])))
    assert parse_prover9("Big") == Atom("Big", [])
    assert parse_prover9("(P(a) & -Q(b))") == And(
        Atom("P", [Constant("a")]), Not(Atom("Q", [Constant("b")])))
    assert parse_prover9("(X >= a)") == Atom("≥", [Variable("x"), Constant("a")])


def test_prover9_trailing_period_optional():
    assert parse_prover9("P(a).") == parse_prover9("P(a)")


@pytest.mark.parametrize("bad", ["(all X", "p(a) &", "- ->", "(("])
def test_prover9_rejects_malformed(bad):
    with pytest.raises(Prover9ParsingError):
        parse_prover9(bad)


# ---------------------------------------------------------------------------
# Prover9 whole-file reader
# ---------------------------------------------------------------------------

def test_prover9_problem_file():
    from unicode_fol_kit import parse_prover9_problem, Prover9Formula
    text = """
    % Socrates is mortal
    set(prolog_style_variables).
    assign(max_seconds, 30).
    formulas(assumptions).
      all X (man(X) -> mortal(X)).
      man(socrates).
    end_of_list.
    formulas(goals).
      mortal(socrates).
    end_of_list.
    """
    recs = parse_prover9_problem(text)
    assert all(isinstance(r, Prover9Formula) for r in recs)
    # the set/assign directives are recognised and skipped
    assert len(recs) == 3
    assert recs[0].role == "assumptions"
    assert recs[0].formula == Quantifier(
        "∀", Variable("x"),
        Implies(Atom("man", [Variable("x")]), Atom("mortal", [Variable("x")])))
    assert recs[1].role == "assumptions"
    assert recs[1].formula == Atom("man", [Constant("socrates")])
    assert recs[2].role == "goals"
    assert recs[2].formula == Atom("mortal", [Constant("socrates")])


def test_prover9_problem_bare_and_empty():
    from unicode_fol_kit import parse_prover9_problem
    bare = parse_prover9_problem("P(a).\n-Q(b).")
    assert [r.role for r in bare] == ["", ""]
    assert bare[1].formula == Not(Atom("Q", [Constant("b")]))
    # an empty list yields no formulas
    assert parse_prover9_problem("formulas(sos). end_of_list.") == []


def test_prover9_problem_round_trip_random():
    rng = random.Random(99)
    conn = ["not", "and", "or", "imp", "iff"]
    from unicode_fol_kit import parse_prover9_problem
    for _ in range(200):
        f = _rand_formula(rng, rng.randint(1, 3), [], connectives=conn)
        text = f"formulas(sos).\n  {f.to_prover9()}.\nend_of_list.\n"
        recs = parse_prover9_problem(text)
        assert len(recs) == 1 and recs[0].role == "sos"
        assert recs[0].formula == f, f.to_unicode_str()


@pytest.mark.parametrize("bad", [
    "formulas(sos).\n  p(a).\nq(b).",          # missing end_of_list
    "formulas(g).\n  p(a).\nend_of_listX.",    # typo'd end marker
    "p(a).\nend_of_list.",                     # stray end_of_list
    "formulas().\nend_of_list.",               # malformed header (no list name)
])
def test_prover9_problem_rejects_malformed_lists(bad):
    # A malformed list structure is a hard error — NOT silently degraded to bare
    # formulas with the role information lost (the old Earley-backtracking behaviour).
    from unicode_fol_kit import parse_prover9_problem
    with pytest.raises(Prover9ParsingError):
        parse_prover9_problem(bad)


def test_prover9_problem_skips_op_directive_and_keeps_decimals():
    from unicode_fol_kit import parse_prover9_problem
    recs = parse_prover9_problem(
        "set(prolog_style_variables).\nop(800, infix, foo).\nlt(x, 3.14).")
    # set/op directives are skipped; the decimal point is not a statement terminator.
    # (lowercase x is a Prover9 constant; lt is an ordinary predicate.)
    assert len(recs) == 1
    assert recs[0].formula == Atom("lt", [Constant("x"), Number(3.14)])


# ---------------------------------------------------------------------------
# Z3
# ---------------------------------------------------------------------------

def test_from_z3_semantic_round_trip():
    rng = random.Random(77)
    conn = ["not", "and", "or", "xor", "imp", "iff"]
    for _ in range(500):
        f = _rand_formula(rng, rng.randint(1, 4), [], connectives=conn, comparisons=False)
        g = from_z3(f.to_z3())
        assert is_valid(Iff(f, g)), f"{f.to_unicode_str()}  !=  {g.to_unicode_str()}"


def test_from_z3_structural_spot_checks():
    x, a, b = Variable("x"), Constant("a"), Constant("b")
    assert from_z3(Quantifier("∀", x, Atom("P", [x])).to_z3()) == \
        Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    assert from_z3(Atom("≠", [a, b]).to_z3()) == Atom("≠", [Constant("a"), Constant("b")])
    assert from_z3(Xor(Atom("P", [a]), Atom("Q", [a])).to_z3()) == \
        Xor(Atom("P", [Constant("a")]), Atom("Q", [Constant("a")]))
    assert from_z3(Iff(Atom("P", [a]), Atom("Q", [a])).to_z3()) == \
        Iff(Atom("P", [Constant("a")]), Atom("Q", [Constant("a")]))
    assert from_z3(Atom("P", [Number(5)]).to_z3()) == Atom("P", [Number(5)])


def test_from_z3_eq_versus_iff_by_sort():
    # A == B on individuals is "=", on Booleans is Iff.
    a, b = Constant("a"), Constant("b")
    assert from_z3(Atom("=", [a, b]).to_z3()) == Atom("=", [Constant("a"), Constant("b")])
    assert isinstance(from_z3(Iff(Atom("P", []), Atom("Q", [])).to_z3()), Iff)


def test_parse_smtlib_uninterpreted():
    smt = """
    (declare-sort S 0)
    (declare-fun P (S) Bool)
    (declare-fun a () S)
    (assert (forall ((x S)) (=> (P x) (P a))))
    (assert (P a))
    """
    nodes = parse_smtlib(smt)
    assert len(nodes) == 2
    assert nodes[1] == Atom("P", [Constant("a")])
    assert isinstance(nodes[0], Quantifier)


def test_parse_smtlib_arithmetic():
    nodes = parse_smtlib("(declare-fun x () Int)\n(assert (< x (+ x 1)))\n")
    assert len(nodes) == 1
    # x < x + 1
    assert nodes[0] == Atom("<", [Constant("x"), Function("+", [Constant("x"), Number(1)])])


# ---------------------------------------------------------------------------
# Exports
# ---------------------------------------------------------------------------

def test_importer_exports():
    import unicode_fol_kit as u
    for name in ("parse_tptp", "parse_tptp_formula", "load_tptp", "TptpFormula",
                 "parse_prover9", "parse_prover9_problem", "load_prover9",
                 "Prover9Formula", "from_z3", "parse_smtlib", "load_smtlib"):
        assert hasattr(u, name) and name in u.__all__, name
