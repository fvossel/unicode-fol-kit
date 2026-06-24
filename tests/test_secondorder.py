"""Tests for second-order finite-model semantics (semantics.secondorder).

satisfies_so / holds extend Tarskian satisfaction with second-order PREDICATE
quantification (∀P / ∃P), interpreting a bound predicate variable by enumerating
every relation of its arity over the finite domain.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import Lambda, LambdaVar, Atom, WeakConjunction
from unicode_fol_kit.semantics.secondorder import satisfies_so, holds, _all_relations
from unicode_fol_kit.semantics.tarski import Structure, satisfies as fo_satisfies

SO = MSFLParser(second_order=True)


def _struct(*elems):
    return Structure(domain=set(elems), predicates={})


class TestBasicSecondOrder:
    @pytest.mark.parametrize("formula, expected", [
        ("∃P ∀x P(x)", True),    # take P = the whole domain
        ("∀P ∃x P(x)", False),   # take P = ∅ → no witness
        ("∀x ∀P (P(x) ∨ ¬P(x))", True),   # excluded middle at the object level
        ("∃R ∀x ∀y R(x, y)", True),       # binary: R = all pairs
        ("∀R ∃x ∃y ¬R(x, y)", False),     # binary: take R = all pairs
    ])
    def test_facts(self, formula, expected):
        assert holds(SO.parse(formula), _struct(0, 1)) is expected

    def test_monadic_witness(self):
        # ∃P (P holds of exactly element 0): true over {0,1}
        assert holds(SO.parse("∃P (∃x P(x) ∧ ∃y ¬P(y))"), _struct(0, 1)) is True


class TestArity0Propositional:
    @pytest.mark.parametrize("formula, expected", [
        ("∀P (P → P)", True),    # tautology under both Boolean values of P
        ("∃P P", True),          # take P = true
        ("∀P P", False),         # P = false is a counterexample
        ("∃P (P ∧ ¬P)", False),  # no Boolean value makes P ∧ ¬P true
    ])
    def test_boolean_quantification(self, formula, expected):
        assert holds(SO.parse(formula), _struct(0, 1)) is expected


class TestLeibniz:
    """Identity of indiscernibles holds in finite full second-order models."""

    def test_indiscernibles_are_identical(self):
        f = SO.parse("∀x ∀y (∀P (P(x) ↔ P(y)) → x = y)")
        assert holds(f, _struct(0, 1)) is True
        assert holds(f, _struct(0, 1, 2)) is True

    def test_converse(self):
        f = SO.parse("∀x ∀y (x = y → ∀P (P(x) ↔ P(y)))")
        assert holds(f, _struct(0, 1)) is True


class TestArityInferenceShadowing:
    def test_inferred_arities_under_shadowing(self):
        ast = SO.parse("∀P (P(x) ∧ ∀P P(x, y))")
        assert ast.arity == 1                 # outer P used as P(x)
        assert ast.formula.right.arity == 2   # inner P used as P(x, y), shadows outer

    def test_shadowing_semantics(self):
        # Inner ∀P (binary) is independent of the outer P (unary); the whole
        # formula's truth is determined correctly under both bindings.
        f = SO.parse("∃P (∀x P(x) ∧ ∀P ∃x ∃y ¬P(x, y))")
        # outer P = whole domain satisfies ∀x P(x); inner ∀P(binary) ∃x∃y ¬P(x,y)
        # is FALSE (take inner P = all pairs), so the conjunction is False for
        # every outer P → ∃P ... is False.
        assert holds(f, _struct(0, 1)) is False


class TestEnumerationCrossCheck:
    """satisfies_so of ∀P/∃P must equal AND/OR of the body over every relation."""

    def test_monadic_matches_manual_enumeration(self):
        dom = (0, 1)
        S = _struct(*dom)
        body = SO.parse("∀x P(x)")  # P occurs free here (unbound)

        def body_under(relation):
            st = Structure(domain=set(dom), predicates={("P", 1): set(relation)})
            return fo_satisfies(body, st, {})

        rels = list(_all_relations(dom, 1))
        assert len(rels) == 4  # 2 ** (2 ** 1)
        assert holds(SO.parse("∀P ∀x P(x)"), S) == all(body_under(r) for r in rels)
        assert holds(SO.parse("∃P ∀x P(x)"), S) == any(body_under(r) for r in rels)

    def test_relation_counts(self):
        assert len(list(_all_relations((0, 1), 0))) == 2          # 2 ** (2**0)
        assert len(list(_all_relations((0, 1), 1))) == 4          # 2 ** (2**1)
        assert len(list(_all_relations((0, 1), 2))) == 16         # 2 ** (2**2)


class TestRejections:
    def test_lambda_rejected(self):
        with pytest.raises(NotImplementedError):
            satisfies_so(Lambda(LambdaVar("x"), Atom("P", [])), _struct(0, 1))

    def test_fuzzy_rejected(self):
        with pytest.raises(ValueError):
            satisfies_so(WeakConjunction(Atom("P", []), Atom("Q", [])), _struct(0, 1))
