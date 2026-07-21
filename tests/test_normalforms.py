"""Tests for normal forms (NNF, PNF, CNF, Skolemization) and the Horn check."""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.normalforms import (
    to_nnf, to_pnf, to_cnf, skolemize, is_horn,
    _prenex_split, _clauses, _cnf,
)
from unicode_fol_kit.fol._fol_nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Function, Constant,
)
from unicode_fol_kit.atp import formulas_are_equivalent, is_satisfiable

FOL = MSFLParser()
MSFOL = MSFLParser(many_sorted=True)
MSFL = MSFLParser(many_sorted=True, fuzzy=True)


# ---------------------------------------------------------------------------
# Shape invariants
# ---------------------------------------------------------------------------

class TestNNFShape:
    @pytest.mark.parametrize("formula", [
        "P → Q", "P ↔ Q", "P ⊕ Q", "¬(P ∧ Q)", "¬(P ∨ Q)",
        "¬¬P", "∀x (P(x) → Q(x))", "¬∀x P(x)", "¬∃x P(x)",
        "(P → Q) ∧ (Q ↔ R)",
    ])
    def test_nnf_has_no_implication_or_eq_or_xor(self, formula):
        nnf = to_nnf(FOL.parse(formula))
        for node in nnf.walk():
            assert not isinstance(node, (Implies, Iff, Xor)), f"{node!r} survived in NNF"
            # negation only on atoms
            if isinstance(node, Not):
                assert isinstance(node.formula, Atom), f"¬ wraps non-atom {node.formula!r}"


class TestPNFShape:
    @pytest.mark.parametrize("formula", [
        "∀x (P(x) → Q(x))", "∀x P(x) ∧ ∃y Q(y)", "¬∀x P(x)",
        "∀x ∃y R(x, y)", "(∀x P(x)) → (∃y Q(y))",
    ])
    def test_prefix_then_quantifier_free_matrix(self, formula):
        pnf = to_pnf(FOL.parse(formula))
        prefix, matrix = _prenex_split(pnf)
        # matrix contains no quantifiers
        for node in matrix.walk():
            assert not isinstance(node, Quantifier), "quantifier left in PNF matrix"

    def test_standardized_apart(self):
        # ∀x P(x) ∧ ∀x Q(x): the two x's must be renamed to distinct fresh names.
        pnf = to_pnf(FOL.parse("∀x P(x) ∧ ∀x Q(x)"))
        prefix, _ = _prenex_split(pnf)
        names = [v.name for _, v in prefix]
        assert len(names) == 2
        assert len(set(names)) == 2, f"bound vars not standardized apart: {names}"


class TestCNFShape:
    @pytest.mark.parametrize("formula", [
        "P ∧ (Q ∨ R)", "(P ∨ Q) ∧ (R ∨ S)", "P ∨ (Q ∧ R)",
        "(P ∧ Q) ∨ (R ∧ S)", "¬(P ∧ Q)",
    ])
    def test_matrix_is_conjunction_of_clauses(self, formula):
        cnf = to_cnf(FOL.parse(formula))
        _, matrix = _prenex_split(cnf)
        # every clause is a disjunction of literals (Atom / ¬Atom)
        for clause in _clauses(matrix):
            for lit in clause:
                ok = isinstance(lit, Atom) or (isinstance(lit, Not) and isinstance(lit.formula, Atom))
                assert ok, f"non-literal {lit!r} in CNF clause"


# ---------------------------------------------------------------------------
# Equivalence (Z3 oracle): NNF / PNF / CNF preserve meaning
# ---------------------------------------------------------------------------

class TestEquivalencePreserving:
    CASES = [
        "P ↔ Q", "P ⊕ Q", "(P ∨ Q) → R", "¬(P ∧ Q)",
        "P → Q → R", "(P → Q) ∧ (Q → R)", "¬(P ↔ Q)",
        "∀x (P(x) ↔ Q(x))",
    ]

    @pytest.mark.parametrize("formula", CASES)
    def test_nnf_equivalent(self, formula):
        f = FOL.parse(formula)
        assert formulas_are_equivalent(f, to_nnf(f))

    @pytest.mark.parametrize("formula", CASES)
    def test_pnf_equivalent(self, formula):
        f = FOL.parse(formula)
        assert formulas_are_equivalent(f, to_pnf(f))

    @pytest.mark.parametrize("formula", CASES)
    def test_cnf_equivalent(self, formula):
        f = FOL.parse(formula)
        assert formulas_are_equivalent(f, to_cnf(f))


# ---------------------------------------------------------------------------
# Skolemization: equisatisfiable, existentials removed
# ---------------------------------------------------------------------------

class TestSkolemize:
    def test_existential_becomes_constant(self):
        sk = skolemize(FOL.parse("∃x P(x)"))
        # ∃ dropped, P applied to a Skolem constant
        assert isinstance(sk, Atom)
        assert isinstance(sk.args[0], Constant)

    def test_existential_under_universal_becomes_function(self):
        sk = skolemize(FOL.parse("∀x ∃y Loves(x, y)"))
        prefix, matrix = _prenex_split(sk)
        # only a universal remains in the prefix
        assert all(t in ("∀", "forall") for t, _ in prefix)
        # the existential is now a Skolem function of the universal
        skolem_term = matrix.args[1]
        assert isinstance(skolem_term, Function)
        assert len(skolem_term.args) == 1

    def test_no_existentials_remain(self):
        sk = skolemize(FOL.parse("∀x ∃y ∃z R(x, y, z)"))
        for node in sk.walk():
            if isinstance(node, Quantifier):
                assert node.type in ("∀", "forall")

    @pytest.mark.parametrize("formula", ["∃x P(x)", "P ∧ Q", "∃x (P(x) ∨ Q(x))"])
    def test_satisfiability_preserved(self, formula):
        f = FOL.parse(formula)
        assert is_satisfiable(f) == is_satisfiable(skolemize(f))


# ---------------------------------------------------------------------------
# Mode coverage: sorted / fuzzy inputs are reduced first
# ---------------------------------------------------------------------------

class TestModeReduction:
    def test_sorted_input_nnf(self):
        nnf = to_nnf(MSFOL.parse("∀x:Human (P(x) → Q(x))"))
        for node in nnf.walk():
            assert not isinstance(node, Implies)

    def test_fuzzy_input_rejected_with_pointer(self):
        # The classical collapse changes the LOGIC (fuzzy P ∨ ¬P is not
        # Łukasiewicz-valid, its classical image is), so the normal forms
        # refuse fuzzy input instead of silently deciding the wrong logic.
        f = MSFL.parse("P(x) → Q(x)")
        with pytest.raises(TypeError, match="fuzzy_is_valid"):
            to_cnf(f)
        with pytest.raises(TypeError, match="Łukasiewicz"):
            to_nnf(f)

    def test_fuzzy_explicit_collapse_still_works(self):
        from unicode_fol_kit.fol import to_fol
        f = MSFL.parse("P(x) → Q(x)")
        collapsed = to_fol(f)                # the explicit, documented opt-in
        assert formulas_are_equivalent(collapsed, to_cnf(collapsed))


# ---------------------------------------------------------------------------
# Horn check (syntactic / clausal)
# ---------------------------------------------------------------------------

class TestHorn:
    @pytest.mark.parametrize("formula, expected", [
        ("P", True),
        ("¬P", True),
        ("P ∧ Q", True),
        ("P ∨ Q", False),
        ("P → Q", True),
        ("(P ∧ Q) → R", True),
        ("P → (Q ∧ R)", True),
        ("P → (Q ∨ R)", False),
        ("¬P ∨ ¬Q", True),
        ("∀x (Body(x) → Head(x))", True),
        ("∀x (P(x) → (Q(x) ∨ R(x)))", False),
        ("∀x ∃y Loves(x, y)", True),
    ])
    def test_is_horn(self, formula, expected):
        assert is_horn(FOL.parse(formula)) is expected

    def test_horn_accepts_sorted_rejects_fuzzy(self):
        assert is_horn(MSFOL.parse("∀x:Human (Body(x) → Head(x))")) is True
        with pytest.raises(TypeError, match="Łukasiewicz"):
            is_horn(MSFL.parse("P(x) → Q(x)"))


# ---------------------------------------------------------------------------
# Idempotence
# ---------------------------------------------------------------------------

class TestIdempotence:
    @pytest.mark.parametrize("formula", ["P ↔ Q", "∀x (P(x) → Q(x))", "(P ∨ Q) ∧ R"])
    def test_nnf_idempotent(self, formula):
        once = to_nnf(FOL.parse(formula))
        assert to_nnf(once) == once
