r"""Capture-avoiding renaming mints names the kit's own parser reads back -- and never captures.

Alpha-renaming used to mint ``base_N``, so ``substitute`` on ``∀y R(x, y)`` with
``x := y`` printed ``∀y_0 R(y, y_0)``, text that ``api.parse_any`` rejects: VARIABLE is
one term-valued letter followed by ASCII digits, no underscore. The renaming now goes
through ``fresh_variable_like`` / ``fresh_like``, and the same shape is used by the
counting expansion's witnesses and by the sequent calculus' temporaries.

Two properties are checked at EVERY site, and the second matters more than the first:

1. the minted name is legal (the formula reads back);
2. the renaming still avoids capture. The new shape is far more collision-prone than
   ``y_0`` ever was -- ``y0`` and ``x1`` are ordinary user names -- so a site whose
   ``avoid`` set only holds FREE variables, which was harmless while the fresh name was
   ``y_0``, now picks a name that an inner binder already uses and captures the
   occurrences it just moved. Each family below has a case where the first free
   candidate (``y0``) is taken by an inner BOUND binder, by a FREE variable of the body
   and (for the IF-logic family) by a slash name, so the naive choice would capture.

Every expectation is hand-derived in the comment above it; none is a copy of what the
code printed. Two independent oracles back the exact expectations: a Tarski evaluator
written in this file (the substitution lemma ``⟦φ[x:=t]⟧_ρ = ⟦φ⟧_{ρ[x↦⟦t⟧_ρ]}`` checked
over every relation on a two-element domain), and the kit's own parser.
"""

import importlib
import itertools
import re

import pytest

from unicode_fol_kit import MSFLParser, api, to_fol
from unicode_fol_kit.atp.fitch import Proof, line, premise, verify_proof, _subst_var
from unicode_fol_kit.atp.sequent import _subst_pred, _subst_simultaneous
from unicode_fol_kit.fol._identifiers import (
    fresh_variables, name_pattern, predicate_pattern, variable_names, variable_pattern,
)
from unicode_fol_kit.fol._msfl_nodes import beta_reduce, substitute
from unicode_fol_kit.fol.nodes import (
    And, Application, Atom, Cardinality, Constant, Count, Implies, Lambda, LambdaVar,
    Not, Number, Or, Quantifier, SecondOrderQuantifier, SlashedExists, SortedCardinality,
    SortedCount, SortedQuantifier, Variable, free_variables,
)

# ``unicode_fol_kit.atp.sequent`` is also a function re-exported by the package, which
# shadows the submodule on attribute access -- import the module by name.
sequent_mod = importlib.import_module("unicode_fol_kit.atp.sequent")

x, y, z = Variable("x"), Variable("y"), Variable("z")
y0, y1 = Variable("y0"), Variable("y1")
_VARIABLE = re.compile(variable_pattern())
_NAME = re.compile(name_pattern())
_PREDICATE = re.compile(predicate_pattern())


def R(*args):
    return Atom("R", tuple(args))


def S(*args):
    return Atom("S", tuple(args))


def T(*args):
    return Atom("T", tuple(args))


# --------------------------------------------------------------------------- #
# The binder families that capture-avoiding substitution renames.
# --------------------------------------------------------------------------- #

class Family:
    """One binder shape: how to build it around a body and how to build an INNER one."""

    def __init__(self, name, bind, inner, sorted_=False, mode=None):
        self.name, self.bind, self.inner = name, bind, inner
        self.sorted_, self.mode = sorted_, mode

    def __repr__(self):
        return self.name


def _plain_inner(v, body):
    return Quantifier("∃", v, body)


def _sorted_inner(v, body):
    return SortedQuantifier("∃", v, "S", body)


FAMILIES = [
    Family("forall", lambda v, b: Quantifier("∀", v, b), _plain_inner),
    Family("exists", lambda v, b: Quantifier("∃", v, b), _plain_inner),
    Family("sorted", lambda v, b: SortedQuantifier("∀", v, "S", b), _sorted_inner, True),
    Family("count", lambda v, b: Count("ge", Number(2), v, b), _plain_inner),
    Family("sorted_count", lambda v, b: SortedCount("ge", Number(2), v, "S", b),
           _sorted_inner, True),
    Family("slashed", lambda v, b: SlashedExists(v, ("z",), b), _plain_inner),
    # a cardinality is a TERM, so it sits in a comparison
    Family("cardinality", lambda v, b: Atom(">", (Cardinality(v, b), Number(2))),
           _plain_inner),
    Family("sorted_cardinality",
           lambda v, b: Atom(">", (SortedCardinality(v, "S", b), Number(2))),
           _sorted_inner, True),
]

# The two implementations of first-order substitution: the core one (_msfl_nodes._subst,
# behind ``substitute``) and the Fitch checker's own copy (atp.fitch._subst_var).
SUBSTITUTIONS = [pytest.param(substitute, id="core"), pytest.param(_subst_var, id="fitch")]


def _reads_back(node):
    """The text ``node`` prints parses, and parses to the SAME structure."""
    text = node.to_unicode_str()
    result = api.parse_any(text)
    assert result.ok, f"the kit printed text it cannot read back: {text!r} {result.errors}"
    assert result.formula.to_dict() == node.to_dict(), (
        f"{text!r} parsed, but as a different formula")
    return text


def _legal_variables(node):
    for name in variable_names(node):
        assert _VARIABLE.fullmatch(name), f"{name!r} is no VARIABLE of this kit"


# --------------------------------------------------------------------------- #
# Hand-derived cases, once per binder family and per substitution implementation.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("subst", SUBSTITUTIONS)
@pytest.mark.parametrize("fam", FAMILIES, ids=repr)
class TestRenamedBinderIsLegalAndFresh:
    def test_plain_capture_is_renamed_to_y0(self, fam, subst):
        # φ = B y. R(x, y), substitute x := y.
        #   the replacement's free variable y would be captured by B y, so the binder
        #   is renamed; avoid = {y} ∪ names(R(x, y)) = {x, y}; the first legal
        #   candidate of the kit's shape is y0.
        #   φ[x:=y] = B y0. R(y, y0), and y stays free.
        phi = fam.bind(y, R(x, y))
        got = subst(phi, x, y)
        assert got == fam.bind(y0, R(y, y0))
        _reads_back(got)
        _legal_variables(got)
        assert y in free_variables(got)          # the incoming y was not captured

    def test_candidate_taken_by_an_inner_bound_binder(self, fam, subst):
        # φ = B y. (R(x, y) ∧ ∃y0 S(y, y0)), substitute x := y.
        #   avoid = {y} ∪ {x, y, y0}: y0 is BOUND inside the scope, so the first free
        #   candidate is y1. Moving the occurrences of y onto y0 would put S's first
        #   argument under ∃y0, i.e. ∃y0 S(y0, y0): a capture of the renamed y.
        phi = fam.bind(y, And(R(x, y), fam.inner(y0, S(y, y0))))
        got = subst(phi, x, y)
        assert got == fam.bind(y1, And(R(y, y1), fam.inner(y0, S(y1, y0))))
        _reads_back(got)

    def test_candidate_taken_by_a_free_variable_of_the_body(self, fam, subst):
        # φ = B y. (R(x, y) ∧ T(y0)), y0 free in the body, substitute x := y.
        #   avoid = {y} ∪ {x, y, y0}: renaming onto y0 would bind the free y0 of T(y0).
        phi = fam.bind(y, And(R(x, y), T(y0)))
        got = subst(phi, x, y)
        assert got == fam.bind(y1, And(R(y, y1), T(y0)))
        _reads_back(got)
        assert y0 in free_variables(got)

    def test_no_capture_means_no_renaming(self, fam, subst):
        # x := w does not clash with the binder y, so nothing is renamed (the fix must
        # not rename gratuitously).
        w = Variable("w")
        assert subst(fam.bind(y, R(x, y)), x, w) == fam.bind(y, R(w, y))

    def test_a_rebinding_binder_stops_the_substitution(self, fam, subst):
        # B x. R(x, y) rebinds the target x: nothing below it changes, nothing renamed.
        phi = fam.bind(x, R(x, y))
        assert subst(phi, x, y) == phi


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
def test_slash_name_is_avoided_too(subst):
    # φ = ∃y/{y0}. R(x, y), substitute x := y. The slash set names the enclosing
    # variable y0 (a plain string, invisible to the matrix), so a fresh binder called
    # y0 would silently make the existential independent of ITSELF. avoid ∋ y0 -> y1,
    # and the independence set is left exactly as it was.
    phi = SlashedExists(y, ("y0",), R(x, y))
    got = subst(phi, x, y)
    assert got == SlashedExists(y1, ("y0",), R(y, y1))
    assert got.slashed == ("y0",)
    _reads_back(got)


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
def test_a_binder_not_minted_by_the_kit_is_still_renamed_to_a_legal_name(subst):
    # Importers and hand-built nodes carry names the VARIABLE terminal does not accept
    # (a Prolog-style X, a leading underscore). Renaming such a binder is still plain
    # alpha-equivalence and must not raise; the NEW name is legal even though the old
    # one was not.
    for base, letter in (("X", "x"), ("_tmp", "x"), ("y_1", "y")):
        v = Variable(base)
        phi = Quantifier("∀", v, R(x, v))
        got = subst(phi, x, v)
        fresh = got.variable.name
        assert fresh == f"{letter}0", (base, fresh)
        assert _VARIABLE.fullmatch(fresh)
        assert got == Quantifier("∀", Variable(fresh), R(v, Variable(fresh)))


def test_substitution_is_deterministic():
    phi = Quantifier("∀", y, And(R(x, y), Quantifier("∃", y0, S(y, y0))))
    first = substitute(phi, x, y)
    assert [substitute(phi, x, y) for _ in range(3)] == [first] * 3
    assert first.to_unicode_str() == "∀y1 (R(y, y1) ∧ ∃y0 S(y1, y0))"


# --------------------------------------------------------------------------- #
# Oracle 2: a Tarski evaluator, and the substitution lemma.
# --------------------------------------------------------------------------- #

DOMAIN = (0, 1)


def _truth(node, env, rels):
    """⟦node⟧ in the structure DOMAIN with the relations ``rels`` (name -> callable)."""
    if isinstance(node, Atom):
        args = tuple(env[a.name] for a in node.args)
        if node.predicate == "≠":
            return args[0] != args[1]
        return bool(rels[node.predicate](*args))
    if isinstance(node, Not):
        return not _truth(node.formula, env, rels)
    if isinstance(node, And):
        return _truth(node.left, env, rels) and _truth(node.right, env, rels)
    if isinstance(node, Or):
        return _truth(node.left, env, rels) or _truth(node.right, env, rels)
    if isinstance(node, Implies):
        return (not _truth(node.left, env, rels)) or _truth(node.right, env, rels)
    if isinstance(node, Quantifier):
        values = (_truth(node.formula, {**env, node.variable.name: d}, rels) for d in DOMAIN)
        return all(values) if node.type == "∀" else any(values)
    if isinstance(node, Count):
        n = sum(1 for d in DOMAIN
                if _truth(node.formula, {**env, node.variable.name: d}, rels))
        return {"ge": n >= node.n.value, "le": n <= node.n.value,
                "eq": n == node.n.value}[node.op]
    raise AssertionError(f"evaluator does not cover {type(node).__name__}")


def _binary_relations():
    pairs = list(itertools.product(DOMAIN, DOMAIN))
    for bits in itertools.product((False, True), repeat=len(pairs)):
        table = dict(zip(pairs, bits))
        yield lambda a, b, table=table: table[(a, b)]


def _unary_relations():
    for bits in itertools.product((False, True), repeat=len(DOMAIN)):
        yield lambda a, bits=bits: bits[a]


SEMANTIC_FAMILIES = [f for f in FAMILIES if f.name in ("forall", "exists", "count")]


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
@pytest.mark.parametrize("fam", SEMANTIC_FAMILIES, ids=repr)
def test_substitution_lemma_over_every_structure_on_two_elements(fam, subst):
    # ⟦φ[x:=y]⟧ at y↦d must equal ⟦φ⟧ at x↦d, for every R, S and d. The formula is the
    # collision case (y0 is bound inside), where a capture would change the truth value
    # in some structure -- checked here against the definition of substitution, not
    # against any particular choice of fresh name.
    phi = fam.bind(y, And(R(x, y), fam.inner(y0, S(y, y0))))
    got = subst(phi, x, y)
    checked = 0
    for r in _binary_relations():
        for s in _binary_relations():
            for d in DOMAIN:
                rels = {"R": r, "S": s}
                assert _truth(got, {"y": d}, rels) == _truth(phi, {"x": d}, rels)
                checked += 1
    assert checked == 16 * 16 * 2


@pytest.mark.parametrize("subst", SUBSTITUTIONS)
def test_the_naive_choice_really_does_change_the_meaning(subst):
    # Guard on the oracle itself: capturing (keeping the binder y, or renaming onto the
    # inner y0) is a DIFFERENT formula, and the evaluator tells the two apart.
    phi = Quantifier("∀", y, And(R(x, y), Quantifier("∃", y0, S(y, y0))))
    captured_by_keeping_y = Quantifier("∀", y, And(R(y, y), Quantifier("∃", y0, S(y, y0))))
    captured_by_y0 = Quantifier("∀", y0, And(R(y, y0), Quantifier("∃", y0, S(y0, y0))))
    correct = subst(phi, x, y)
    differs = {"keep": False, "y0": False}
    for r in _binary_relations():
        for s in _binary_relations():
            for d in DOMAIN:
                rels = {"R": r, "S": s}
                truth = _truth(correct, {"y": d}, rels)
                if truth != _truth(captured_by_keeping_y, {"y": d}, rels):
                    differs["keep"] = True
                if truth != _truth(captured_by_y0, {"y": d}, rels):
                    differs["y0"] = True
    assert differs == {"keep": True, "y0": True}


# --------------------------------------------------------------------------- #
# Lambda parameters keep their kind.
# --------------------------------------------------------------------------- #

def _lam(param, body):
    return Lambda(LambdaVar(param), body)


def _app(f, a):
    return Application(f, a)


class TestLambdaParameterRenaming:
    def test_variable_parameter(self):
        # (λx. λy. x)(y): the λy binder would capture the free LambdaVar y of the
        # argument. avoid = {y} ∪ names(λy. x) = {y, x}; y is a VARIABLE-shaped
        # parameter, so the candidate is y0. Result λy0. y.
        got = beta_reduce(_app(_lam("x", _lam("y", LambdaVar("x"))), LambdaVar("y")))
        assert got == _lam("y0", LambdaVar("y"))
        assert _VARIABLE.fullmatch(got.param.name)
        assert api.parse_any(got.to_unicode_str()).ok
        assert LambdaVar("y") in free_variables(got)

    def test_variable_parameter_with_a_free_lambda_variable_in_the_body(self):
        # (λx. λy. y0 x)(y): y0 is free in the body of λy, so renaming onto y0 would
        # capture it. avoid = {y} ∪ {y0, x} -> y1. Result λy1. y0 y.
        body = _app(LambdaVar("y0"), LambdaVar("x"))
        got = beta_reduce(_app(_lam("x", _lam("y", body)), LambdaVar("y")))
        assert got == _lam("y1", _app(LambdaVar("y0"), LambdaVar("y")))
        assert {LambdaVar("y"), LambdaVar("y0")} <= free_variables(got)
        assert api.parse_any(got.to_unicode_str()).ok

    def test_predicate_parameter_stays_a_predicate(self):
        # (λx. λP. P x)(P): the λP binder captures the free P of the argument. P is a
        # PREDICATE-shaped parameter and is applied as a head, so it must stay an
        # uppercase-led name: P_0. Result λP_0. P_0 P.
        body = _app(LambdaVar("P"), LambdaVar("x"))
        got = beta_reduce(_app(_lam("x", _lam("P", body)), LambdaVar("P")))
        assert got == _lam("P_0", _app(LambdaVar("P_0"), LambdaVar("P")))
        assert _PREDICATE.fullmatch(got.param.name)
        assert api.parse_any(got.to_unicode_str()).ok

    def test_predicate_candidate_taken_in_the_body(self):
        # as above, but P_0 is already a free lambda variable of the body: -> P_1.
        body = _app(_app(LambdaVar("P_0"), LambdaVar("P")), LambdaVar("x"))
        got = beta_reduce(_app(_lam("x", _lam("P", body)), LambdaVar("P")))
        assert got.param.name == "P_1"
        assert LambdaVar("P_0") in free_variables(got)

    def test_name_parameter_stays_a_name(self):
        # (λx. λfoo. foo x)(foo): foo is a NAME-shaped parameter -> foo_0.
        body = _app(LambdaVar("foo"), LambdaVar("x"))
        got = beta_reduce(_app(_lam("x", _lam("foo", body)), LambdaVar("foo")))
        assert got == _lam("foo_0", _app(LambdaVar("foo_0"), LambdaVar("foo")))
        assert _NAME.fullmatch(got.param.name)
        assert api.parse_any(got.to_unicode_str()).ok

    def test_a_parameter_the_parser_could_not_have_made_gets_a_legal_variable(self):
        # x_0 is none of VARIABLE / NAME / PREDICATE; renamed, it becomes a legal
        # variable (letter x, first free digit run).
        got = beta_reduce(_app(_lam("x", _lam("x_0", LambdaVar("x"))), LambdaVar("x_0")))
        assert got == _lam("x0", LambdaVar("x_0"))

    def test_object_variable_and_lambda_variable_share_the_namespace(self):
        # A logical Variable y0 in the body is a name the fresh LAMBDA parameter must
        # avoid too: re-reading ``λy0. … y0 …`` would resolve the logical y0 to the
        # parameter. (λx. λy. R(y0)) with a logical Variable y0 in R, x := y -> y1.
        body = Atom("R", (Variable("y0"), Variable("x")))
        term = _app(_lam("x", _lam("y", body)), LambdaVar("y"))
        got = beta_reduce(term)
        assert got.param.name == "y1"


# --------------------------------------------------------------------------- #
# The Count expansion's witnesses.
# --------------------------------------------------------------------------- #

def P1(v):
    return Atom("P", (v,))


def _count(op, n, matrix, var=x):
    return Count(op, Number(n), var, matrix)


def _ne(a, b):
    return Atom("≠", (a, b))


class TestCountExpansionWitnesses:
    def test_at_least_two_is_the_guides_formula_in_the_readable_shape(self):
        # ∃≥2 x P(x): witnesses x0, x1; conjuncts P(x0), P(x1), x0 ≠ x1.
        #   ∃x0 ∃x1 (P(x0) ∧ P(x1) ∧ x0 ≠ x1)
        x0, x1 = Variable("x0"), Variable("x1")
        got = to_fol(_count("ge", 2, P1(x)))
        assert got == Quantifier("∃", x0, Quantifier("∃", x1, And(
            And(P1(x0), P1(x1)), _ne(x0, x1))))
        assert _reads_back(got) == "∃x0 ∃x1 (P(x0) ∧ P(x1) ∧ x0 ≠ x1)"

    def test_the_guide_states_what_the_code_produces(self):
        import pathlib
        guide = (pathlib.Path(__file__).parent.parent / "docs" / "guide"
                 / "transforms.md").read_text(encoding="utf-8")
        printed = to_fol(_count("ge", 2, P1(x))).to_unicode_str()
        assert f"`{printed}`" in guide
        assert "x_0" not in guide

    def test_at_most_and_exactly_continue_the_numbering(self):
        # ∃≤1 x P(x) = ¬(∃≥2 x P(x)): witnesses x0, x1.
        # ∃=1 x P(x) = ∃≥1 ∧ ¬∃≥2: the SECOND expansion continues where the first
        # stopped (x1, x2), so the two never share a witness name.
        assert to_fol(_count("le", 1, P1(x))).to_unicode_str() == \
            "¬∃x0 ∃x1 (P(x0) ∧ P(x1) ∧ x0 ≠ x1)"
        eq = to_fol(_count("eq", 1, P1(x)))
        assert eq.to_unicode_str() == \
            "∃x0 P(x0) ∧ ¬∃x1 ∃x2 (P(x1) ∧ P(x2) ∧ x1 ≠ x2)"
        _reads_back(eq)

    def test_at_least_zero(self):
        # '≥ 0' is ∃x0 (P(x0) ∨ ¬P(x0)), valid on a non-empty domain.
        got = to_fol(_count("ge", 0, P1(x)))
        assert got.to_unicode_str() == "∃x0 (P(x0) ∨ ¬P(x0))"
        _reads_back(got)

    def test_witnesses_are_named_after_the_counting_variable(self):
        v = Variable("v")
        got = to_fol(_count("ge", 2, P1(v), var=v))
        assert got.to_unicode_str() == "∃v0 ∃v1 (P(v0) ∧ P(v1) ∧ v0 ≠ v1)"

    def test_a_free_variable_of_the_matrix_is_not_reused(self):
        # ∃≥2 x R(x, x0): x0 is FREE in the matrix. A witness called x0 would turn
        # R(x_i, x0) into R(x0, x0): a different formula. avoid ∋ x0 -> x1, x2.
        x0, x1, x2 = Variable("x0"), Variable("x1"), Variable("x2")
        got = to_fol(_count("ge", 2, R(x, x0)))
        assert got == Quantifier("∃", x1, Quantifier("∃", x2, And(
            And(R(x1, x0), R(x2, x0)), _ne(x1, x2))))
        assert x0 in free_variables(got)
        _reads_back(got)

    def test_a_bound_name_of_the_matrix_is_not_reused(self):
        # ∃≥2 x ∃x0 R(x, x0): x0 is BOUND in the matrix. Witnesses x1, x2 avoid it, so
        # no inner binder has to be renamed away to make room.
        x0, x1, x2 = Variable("x0"), Variable("x1"), Variable("x2")
        got = to_fol(_count("ge", 2, Quantifier("∃", x0, R(x, x0))))
        assert got == Quantifier("∃", x1, Quantifier("∃", x2, And(
            And(Quantifier("∃", x0, R(x1, x0)), Quantifier("∃", x0, R(x2, x0))),
            _ne(x1, x2))))
        _reads_back(got)

    def test_sorted_count_keeps_its_guard(self):
        # ∃≥1 x:S P(x) -> ∃x0 (S(x0) ∧ P(x0))
        got = to_fol(MSFLParser(many_sorted=True).parse("∃≥1 x:S P(x)"))
        assert got.to_unicode_str() == "∃x0 (S(x0) ∧ P(x0))"
        _reads_back(got)

    @pytest.mark.parametrize("op", ["ge", "le", "eq"])
    @pytest.mark.parametrize("n", [0, 1, 2, 3])
    def test_the_expansion_counts_correctly_in_every_structure(self, op, n):
        # Oracle: the expansion is true in a structure iff the NUMBER of elements in P
        # compares as the operator says, for every P over a three-element domain.
        # (Three elements make ∃≥3 satisfiable and ∃≤2 refutable.)
        global DOMAIN
        saved, DOMAIN = DOMAIN, (0, 1, 2)
        try:
            expansion = to_fol(_count(op, n, P1(x)))
            for bits in itertools.product((False, True), repeat=3):
                size = sum(bits)
                expected = {"ge": size >= n, "le": size <= n, "eq": size == n}[op]
                assert _truth(expansion, {}, {"P": lambda a, bits=bits: bits[a]}) == expected
        finally:
            DOMAIN = saved


# --------------------------------------------------------------------------- #
# The Fitch checker: the renamed instance is the one a user can type.
# --------------------------------------------------------------------------- #

def test_forall_elimination_licenses_the_renamed_instance_and_refuses_the_captured_one():
    # ∀x ∃y R(x, y) ⊢ ∃y0 R(y, y0)  by ∀E with the term y: φ[x:=y] renames the binder.
    # The text ∃y0 R(y, y0) is something a user can now TYPE (it used to be ∃y_0 ...).
    # The captured instance ∃y R(y, y) is NOT entailed (countermodel: R = {(0,1),(1,0)}),
    # and the checker must refuse it.
    parser = MSFLParser()
    premise_formula = parser.parse("∀x ∃y R(x, y)")
    good = Proof(premises=[premise(1, premise_formula)],
                 steps=[line(2, parser.parse("∃y0 R(y, y0)"), "∀E", 1, extra=[y])])
    assert verify_proof(good).ok
    bad = Proof(premises=[premise(1, premise_formula)],
                steps=[line(2, parser.parse("∃y R(y, y)"), "∀E", 1, extra=[y])])
    assert not verify_proof(bad).ok


# --------------------------------------------------------------------------- #
# The sequent calculus: comprehension instantiation and simultaneous substitution.
# --------------------------------------------------------------------------- #

class TestSequentRenaming:
    def test_comprehension_binder_renamed_to_a_legal_name_that_avoids_inner_binders(self):
        # A = ∀v (X(v) ∧ ∃v0 W(v, v0)); instantiate X := λz. R(v, z) (v is FREE in the
        # comprehension body). The binder ∀v would capture it, so it is renamed.
        #   avoid = psi_fv {v} ∪ names(body) {v, v0} ∪ {v}: v0 is BOUND inside, so the
        #   fresh name is v1 (v0 would capture the renamed occurrences under ∃v0).
        #   X(v1) becomes ψ[z:=v1] = R(v, v1).
        #   Result: ∀v1 (R(v, v1) ∧ ∃v0 W(v1, v0)).
        v, v0, v1, w = Variable("v"), Variable("v0"), Variable("v1"), Variable("z")
        body = Quantifier("∀", v, And(Atom("X", (v,)), Quantifier("∃", v0, Atom("W", (v, v0)))))
        got = _subst_pred(body, "X", (w,), R(v, w))
        assert got == Quantifier("∀", v1, And(R(v, v1), Quantifier("∃", v0, Atom("W", (v1, v0)))))
        _reads_back(got)

    def test_comprehension_lemma_over_every_structure_on_two_elements(self):
        # Oracle: ⟦A[X:=λz.R(v,z)]⟧ at v↦d  ==  ⟦A⟧ with X interpreted as {e : R(d, e)}.
        v, v0, w = Variable("v"), Variable("v0"), Variable("z")
        body = Quantifier("∀", v, And(Atom("X", (v,)), Quantifier("∃", v0, Atom("W", (v, v0)))))
        got = _subst_pred(body, "X", (w,), R(v, w))
        count = 0
        for r in _binary_relations():
            for wrel in _binary_relations():
                for d in DOMAIN:
                    expected = _truth(body, {}, {"X": lambda e, r=r, d=d: r(d, e), "W": wrel})
                    assert _truth(got, {"v": d}, {"R": r, "W": wrel}) == expected
                    count += 1
        assert count == 16 * 16 * 2

    def test_slash_set_still_forces_a_different_name(self):
        # ∃v/{v0} X(v) with X := λz. R(v, z): avoid ∋ v0 (slash) -> v1; slash untouched.
        v, v1, z_ = Variable("v"), Variable("v1"), Variable("z")
        got = _subst_pred(SlashedExists(v, ("v0",), Atom("X", (v,))), "X", (z_,), R(v, z_))
        assert got == SlashedExists(v1, ("v0",), R(v, v1))

    def test_simultaneous_substitution_swaps_and_keeps_bound_names(self):
        # ψ = R(x, y) ∧ ∀c0 S(c0, x);  [x := y, y := x] simultaneously.
        #   R(x, y) -> R(y, x);  ∀c0 S(c0, x) -> ∀c0 S(c0, y).
        # The temporaries avoid EVERY name in play, c0 included, so the bound c0 is
        # not renamed on the way through.
        psi = And(R(x, y), Quantifier("∀", Variable("c0"), S(Variable("c0"), x)))
        got = _subst_simultaneous(psi, (x, y), (y, x))
        assert got == And(R(y, x), Quantifier("∀", Variable("c0"), S(Variable("c0"), y)))
        _reads_back(got)

    def test_temporaries_are_legal_distinct_and_avoid_every_name(self, monkeypatch):
        psi = And(R(x, y), Quantifier("∀", Variable("c0"), S(Variable("c0"), x)))
        seen = []
        real = sequent_mod._subst_var

        def spy(formula, var, replacement):
            seen.append((var, replacement))
            return real(formula, var, replacement)

        monkeypatch.setattr(sequent_mod, "_subst_var", spy)
        _subst_simultaneous(psi, (x, y), (y, x))
        # the first len(params) calls route each parameter through its temporary
        temps = [replacement for _, replacement in seen[:2]]
        assert [var for var, _ in seen[:2]] == [x, y]
        names = [t.name for t in temps]
        assert all(_VARIABLE.fullmatch(n) for n in names), names
        assert len(set(names)) == 2
        assert not set(names) & {"x", "y", "c0"}
        # hand-derived: letter c, digits from 0, skipping c0 (bound in ψ): c1, c2
        assert names == ["c1", "c2"]

    def test_temporary_does_not_merge_with_a_free_variable_of_psi(self):
        # ψ = R(x, c0) with c0 FREE, x := d. A temporary called c0 would merge x with the
        # free c0 before the second step. Hand-derived result: R(d, c0).
        d, c0 = Variable("d"), Variable("c0")
        assert _subst_simultaneous(R(x, c0), (x,), (d,)) == R(d, c0)

    def test_instantiating_into_a_capturing_binder_renames_it_legally(self):
        # ψ = ∀c0 S(c0, x), x := c0 (the argument's c0 is free).
        #   taken = {c0, x}: the temporary is c1.
        #   step 1 (x -> c1): no clash with ∀c0.            ∀c0 S(c0, c1)
        #   step 2 (c1 -> c0): ∀c0 would capture c0; avoid = {c0} ∪ {c0, c1} ∪ {c1, c0}
        #     -> c2.                                         ∀c2 S(c2, c0)
        c0 = Variable("c0")
        psi = Quantifier("∀", c0, S(c0, x))
        got = _subst_simultaneous(psi, (x,), (c0,))
        assert got == Quantifier("∀", Variable("c2"), S(Variable("c2"), c0))
        _reads_back(got)

    def test_second_order_binder_names_are_legal_predicates(self):
        # ∀²W X(c): instantiating X := λz. W(c) (W free in the comprehension) renames
        # the second-order binder to W_0 -- an uppercase-led name, legal as a predicate.
        c = Constant("c_a")
        got = _subst_pred(SecondOrderQuantifier("∀", "W", 1, Atom("X", (c,))),
                          "X", (z,), Atom("W", (c,)))
        assert got.predicate == "W_0"
        assert _PREDICATE.fullmatch(got.predicate)
        assert api.parse_any(got.to_unicode_str()).ok

    def test_second_order_candidate_taken_in_the_body(self):
        # as above but W_0 is already applied in the body -> W_1.
        c = Constant("c_a")
        body = SecondOrderQuantifier("∀", "W", 1, And(Atom("X", (c,)), Atom("W_0", (c,))))
        got = _subst_pred(body, "X", (z,), Atom("W", (c,)))
        assert got.predicate == "W_1"
        assert api.parse_any(got.to_unicode_str()).ok


# --------------------------------------------------------------------------- #
# The helpers.
# --------------------------------------------------------------------------- #

class TestIdentifierHelpers:
    def test_fresh_variable_like_keeps_the_letter_and_skips_taken_names(self):
        from unicode_fol_kit.fol._identifiers import fresh_variable_like
        assert fresh_variable_like("y") == "y0"
        assert fresh_variable_like("y", {"y", "y0", "y1"}) == "y2"
        assert fresh_variable_like("y3", {"y0"}) == "y1"      # the digits do not carry over
        assert fresh_variable_like("ś") == "ś0"               # a Unicode letter is a letter

    def test_fresh_variable_like_repairs_a_letter_the_terminal_rejects(self):
        from unicode_fol_kit.fol._identifiers import fresh_variable_like
        assert fresh_variable_like("Y") == "y0"               # lowercased
        assert fresh_variable_like("_tmp") == "x0"            # no usable letter
        assert fresh_variable_like("α") == "x0"               # Greek is a constant here
        assert fresh_variable_like("") == "x0"

    def test_fresh_like_follows_the_kind_of_the_name(self):
        from unicode_fol_kit.fol._identifiers import fresh_like
        assert fresh_like("y") == "y0"
        assert fresh_like("y1", {"y0", "y1"}) == "y2"
        assert fresh_like("P") == "P_0"
        assert fresh_like("P", {"P_0"}) == "P_1"
        assert fresh_like("foo") == "foo_0"
        assert fresh_like("świątek") == "świątek_0"
        assert fresh_like("Has_bond_to") == "Has_bond_to_0"
        assert fresh_like("x_0") == "x0"                      # none of the three kinds
        assert fresh_like("_c_0") == "x0"

    @pytest.mark.parametrize("base", ["y", "y12", "ś", "P", "Q_3", "foo", "dani_Shapiro",
                                      "świątek", "c_alpha"])
    def test_the_minted_name_is_always_in_the_kind_it_replaces(self, base):
        from unicode_fol_kit.fol._identifiers import fresh_like
        pattern = (_VARIABLE if _VARIABLE.fullmatch(base)
                   else _PREDICATE if _PREDICATE.fullmatch(base) else _NAME)
        avoid = set()
        for _ in range(4):                                    # and stays legal as it counts up
            fresh = fresh_like(base, avoid)
            assert pattern.fullmatch(fresh), (base, fresh)
            assert fresh not in avoid and fresh != base
            avoid.add(fresh)

    def test_ascii_fast_path_agrees_with_the_terminal(self):
        # fresh_variables skips the Unicode scan for a-z; it must accept exactly what the
        # real terminal accepts there, and still refuse everything else.
        for letter in "abcdefghijklmnopqrstuvwxyz":
            assert _VARIABLE.fullmatch(letter)
            assert fresh_variables(1, letter=letter) == (f"{letter}0",)
        for bad in ("X", "_", "0", "λ", "μ", "α", "", "ab"):
            with pytest.raises(ValueError, match="not a legal variable name"):
                fresh_variables(1, letter=bad)

    def test_variable_names_sees_lambda_variables_and_slash_names(self):
        body = SlashedExists(y, ("z",), R(x, y))
        assert variable_names(body) == frozenset({"x", "y", "z"})
        lam = _lam("p", _app(LambdaVar("p"), LambdaVar("q")))
        assert variable_names(lam) == frozenset({"p", "q"})
