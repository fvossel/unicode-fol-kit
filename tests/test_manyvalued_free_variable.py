"""A free variable of a quantified many-valued problem is a parameter: one element of the domain.

``Γ ⊨ φ`` is read assignment-wise: a variable that is free in some formula of the problem names
ONE element, the same in every formula. Over the substitutional domain ``{a, b}`` the parameter
is ``a`` or ``b``, and the problem is decided under every assignment (valid, a consequence) or
under some (satisfiable). Without a quantifier the domain says nothing about a variable, and
the atom ``P(x)`` is a letter of its own.

The six rows, derived by hand (``alpha`` is a constant of no domain element):

1. ``P(x) ⊢ P(alpha)``            not a consequence: x = a, P(a) designated, P(alpha) not.
2. ``P(x) ⊢ P(x)``                a consequence: one atom.
3. ``P(x) ⊢ ∃y P(y)``             a consequence: whichever element x is, P of it is a disjunct,
                                  and a disjunct that is designated designates the disjunction.
4. ``∀y P(y) ⊢ P(x)``             a consequence: the conjunction over {a, b} designates both
                                  P(a) and P(b), and x is one of the two.
5. ``⊢ P(x) → P(alpha)``          not valid: x = a, P(a) = 1, P(alpha) = 0 gives 0.
6. ``P(x), Q(y) ⊢ ∀z (P(z) ∧ Q(z))``  not a consequence: x = a, y = b, P(a) = Q(b) = 1, P(b) = 0.
"""

import itertools
import random

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Iff, Implies, Not, Or, Quantifier, Variable, substitute)
from unicode_logic_kit.semantics import manyvalued as mv
from unicode_logic_kit.semantics import matrix as mx

DOMAIN = {"a", "b"}
DOMAIN_SEQUENCE = ("a", "b")
CLASSICAL = MSFLParser()

#: (premises, conclusion, is the conclusion a consequence of the premises) — the six rows.
ROWS = [
    (["P(x)"], "P(alpha)", False),
    (["P(x)"], "P(x)", True),
    (["P(x)"], "∃y P(y)", True),
    (["∀y P(y)"], "P(x)", True),
    ([], "P(x) → P(alpha)", False),
    (["P(x)", "Q(y)"], "∀z (P(z) ∧ Q(z))", False),
]
ROW_IDS = [f"row {i}" for i in range(1, 7)]


def parse(text):
    return CLASSICAL.parse(text)


@pytest.mark.parametrize("logic", ["K3", "LP"])
@pytest.mark.parametrize("premises, conclusion, expected", ROWS, ids=ROW_IDS)
def test_the_six_rows_by_entails(logic, premises, conclusion, expected):
    assert mv.entails([parse(p) for p in premises], parse(conclusion), logic, domain=DOMAIN) is expected


@pytest.mark.parametrize("name, matrix", [("K3", mx.K3_MATRIX), ("LP", mx.LP_MATRIX), ("FDE", mx.FDE_MATRIX)])
@pytest.mark.parametrize("premises, conclusion, expected", ROWS, ids=ROW_IDS)
def test_the_six_rows_by_matrix_entails(name, matrix, premises, conclusion, expected):
    result = mx.matrix_entails([parse(p) for p in premises], parse(conclusion), matrix,
                               domain=DOMAIN_SEQUENCE)
    assert result is expected


def test_the_universal_reading_of_a_parameter_in_lp_is_valid_and_in_k3_is_not():
    # ∀y P(y) → P(x) over {a, b}: LP-valid (the implication has value at least 1/2 whichever of
    # P(a), P(b) the parameter is); K3 has no valid formula built from letters alone (every
    # letter at 1/2 gives 1/2, which K3 does not designate).
    formula = parse("∀y P(y) → P(x)")
    assert mv.is_valid(formula, "LP", domain=DOMAIN) is True
    assert mv.is_valid(formula, "K3", domain=DOMAIN) is False
    assert mx.matrix_is_valid(formula, mx.LP_MATRIX, domain=DOMAIN_SEQUENCE) is True
    assert mx.matrix_is_valid(formula, mx.K3_MATRIX, domain=DOMAIN_SEQUENCE) is False


def test_an_existential_conclusion_of_a_parameter_is_lp_valid():
    assert mv.is_valid(parse("P(x) → ∃y P(y)"), "LP", domain=DOMAIN) is True
    assert mx.matrix_is_valid(parse("P(x) → ∃y P(y)"), mx.LP_MATRIX, domain=DOMAIN_SEQUENCE) is True


def test_two_parameters_over_two_elements_are_not_valid_for_a_universal():
    # x = a, y = b: (P(a) ∧ Q(b)) = 1, ∀z (P(z) ∧ Q(z)) = min(P(a) ∧ Q(a), P(b) ∧ Q(b)) = 0 at P(b) = 0.
    formula = parse("(P(x) ∧ Q(y)) → ∀z (P(z) ∧ Q(z))")
    assert mv.is_valid(formula, "LP", domain=DOMAIN) is False
    assert mx.matrix_is_valid(formula, mx.LP_MATRIX, domain=DOMAIN_SEQUENCE) is False


def test_a_parameter_that_must_be_an_element_of_the_domain_restricts_satisfiability():
    # P(x) ∧ ¬P(ann) ∧ ¬P(bob) ∧ ∀y (P(y) ∨ ¬P(y)) over the domain {ann, bob}.  Read with P(x) a
    # letter of its own it is K3-satisfiable (P(x) = 1, P(ann) = P(bob) = 0). With x one of ann,
    # bob, P(x) is P(ann) or P(bob), and ¬P(ann), ¬P(bob) designate only 0 in K3, so P(x) = 0 is
    # not designated: no assignment satisfies it.
    domain = {"ann", "bob"}
    formula = parse("P(x) ∧ ¬P(ann) ∧ ¬P(bob) ∧ ∀y (P(y) ∨ ¬P(y))")
    assert mv.is_satisfiable(formula, "K3", domain=domain) is False
    assert mx.matrix_is_satisfiable(formula, mx.K3_MATRIX, domain=("ann", "bob")) is False
    # the same without the quantifier: the domain says nothing about x, P(x) is a letter of its own
    letters_only = parse("P(x) ∧ ¬P(ann) ∧ ¬P(bob)")
    assert mv.is_satisfiable(letters_only, "K3", domain=domain) is True
    assert mx.matrix_is_satisfiable(letters_only, mx.K3_MATRIX, domain=("ann", "bob")) is True


def test_a_name_bound_in_one_formula_and_free_in_another_is_a_parameter_only_where_it_is_free():
    # ∀x P(x) binds x; the premise P(x) holds of the parameter x. x = a: P(a) ⊢ ∀x P(x) fails (P(b) = 0).
    premises = [parse("P(x)")]
    conclusion = parse("∀x P(x)")
    assert mv.entails(premises, conclusion, "K3", domain=DOMAIN) is False
    # and ∀x P(x) ⊢ P(x) holds: the bound x of the premise is not the parameter, but P(x) is P(a) or P(b)
    assert mv.entails([conclusion], parse("P(x)"), "K3", domain=DOMAIN) is True


def test_a_free_variable_named_like_a_domain_element_is_still_a_parameter():
    # x is free, and 'x' is also an element of the domain {x, y}: the parameter's instances are
    # P(x) and P(y) (constants), never a mix of the variable and the constant.
    formula = parse("∀z P(z) → P(x)")
    assert mv.is_valid(formula, "LP", domain={"x", "y"}) is True


def test_an_evaluator_takes_the_atom_of_a_free_variable_as_a_key_of_the_valuation():
    # no assignment is chosen by the evaluator: P(x) is one more key
    assert mv.kleene_value(parse("P(x) ∧ ∀y Q(y)"), {"P(x)": 1.0, "Q(a)": 0.5, "Q(b)": 1.0}, domain=DOMAIN) == 0.5
    with pytest.raises(KeyError):
        mv.kleene_value(parse("P(x)"), {"P(a)": 1.0})


def test_too_many_assignments_are_refused_by_name(monkeypatch):
    monkeypatch.setattr(mv, "MAX_MODELS", 3)
    with pytest.raises(ValueError, match="assignments"):
        mv.is_valid(parse("P(x) ∧ Q(y) → ∀z P(z)"), "LP", domain=DOMAIN)   # 2**2 = 4 > 3


# ---------------------------------------------------------------------------
# Differential: the deciders against an oracle that shares none of their grounding
# ---------------------------------------------------------------------------

FREE = (Variable("x"), Variable("y"))
CONSTANTS = (Constant("a"), Constant("b"), Constant("alpha"))
BOUND = Variable("z")


def _atom(rng, bound):
    predicate = rng.choice("PQ")
    terms = list(FREE) + list(CONSTANTS) + ([BOUND] if bound else [])
    return Atom(predicate, [rng.choice(terms)])


def _formula(rng, depth, bound=False):
    if depth == 0:
        return _atom(rng, bound)
    kind = rng.choice(["atom", "not", "and", "or", "implies", "iff", "forall", "exists"])
    if kind == "atom":
        return _atom(rng, bound)
    if kind == "not":
        return Not(_formula(rng, depth - 1, bound))
    if kind in ("forall", "exists") and not bound:
        return Quantifier("∀" if kind == "forall" else "∃", BOUND, _formula(rng, depth - 1, True))
    cls = {"and": And, "or": Or, "implies": Implies, "iff": Iff}.get(kind, And)
    return cls(_formula(rng, depth - 1, bound), _formula(rng, depth - 1, bound))


def _remove_quantifiers(formula):
    """Ground a quantifier over {a, b} by the kit's capture-avoiding substitution (the oracle's own)."""
    if isinstance(formula, Quantifier):
        parts = [_remove_quantifiers(substitute(formula.formula, formula.variable, Constant(d)))
                 for d in sorted(DOMAIN)]
        combine = And if formula.type == "∀" else Or
        return combine(parts[0], parts[1])
    if isinstance(formula, Not):
        return Not(_remove_quantifiers(formula.formula))
    if isinstance(formula, (And, Or, Implies, Iff)):
        return type(formula)(_remove_quantifiers(formula.left), _remove_quantifiers(formula.right))
    return formula


def _free_names(formulas):
    names = set()
    for formula in formulas:
        names |= {n.name for n in formula.walk() if isinstance(n, Variable)}
    return sorted(names - {"z"})


def _designated(logic):
    return {"K3": {1.0}, "LP": {0.5, 1.0}}[logic]


_MAX_LETTERS = 6


def _oracle(premises, conclusion, logic, kind):
    """The consequence / validity / satisfiability the definition gives, by explicit enumeration.

    ``None`` when an instance has more than ``_MAX_LETTERS`` letters (3 ** n valuations is too many).
    """
    formulas = [*premises, conclusion]
    names = _free_names(formulas) if any(f.count(Quantifier) for f in formulas) else []
    assignments = itertools.product(sorted(DOMAIN), repeat=len(names))
    designated = _designated(logic)
    outcomes = []
    for chosen in assignments:
        instance = formulas
        for name, element in zip(names, chosen):
            instance = [substitute(f, Variable(name), Constant(element)) for f in instance]
        ground = [_remove_quantifiers(f) for f in instance]
        keys = sorted({a.to_unicode_str() for f in ground for a in f.atoms()})
        if len(keys) > _MAX_LETTERS:
            return None
        found_countermodel = False
        satisfied = False
        for values in itertools.product((0.0, 0.5, 1.0), repeat=len(keys)):
            valuation = dict(zip(keys, values))
            prem = all(mv.kleene_value(f, valuation) in designated for f in ground[:-1])
            concl = mv.kleene_value(ground[-1], valuation) in designated
            if prem and not concl:
                found_countermodel = True
            if prem and concl:
                satisfied = True
        outcomes.append((found_countermodel, satisfied))
    if kind == "satisfiable":
        return any(satisfied for _, satisfied in outcomes)
    return not any(countermodel for countermodel, _ in outcomes)


@pytest.mark.parametrize("seed", range(10))
def test_the_deciders_agree_with_an_oracle_that_enumerates_the_assignments(seed):
    rng = random.Random(seed)
    compared = 0
    for _ in range(8):
        premise, conclusion = _formula(rng, 2), _formula(rng, 2)
        for logic, matrix in (("K3", mx.K3_MATRIX), ("LP", mx.LP_MATRIX)):
            expected = _oracle([premise], conclusion, logic, "entails")
            if expected is not None:
                assert mv.entails([premise], conclusion, logic, domain=DOMAIN) is expected
                assert mx.matrix_entails([premise], conclusion, matrix, domain=DOMAIN_SEQUENCE) is expected
                compared += 1
            expected_valid = _oracle([], conclusion, logic, "entails")
            if expected_valid is not None:
                assert mv.is_valid(conclusion, logic, domain=DOMAIN) is expected_valid
                assert mx.matrix_is_valid(conclusion, matrix, domain=DOMAIN_SEQUENCE) is expected_valid
                compared += 1
            expected_sat = _oracle([], conclusion, logic, "satisfiable")
            if expected_sat is not None:
                assert mv.is_satisfiable(conclusion, logic, domain=DOMAIN) is expected_sat
                assert mx.matrix_is_satisfiable(conclusion, matrix, domain=DOMAIN_SEQUENCE) is expected_sat
                compared += 1
    assert compared > 0
