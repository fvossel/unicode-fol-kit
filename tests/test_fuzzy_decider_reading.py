"""The Z3 deciders of the fuzzy route read a formula as the evaluator does, or refuse it as it does.

* A comparison atom (``a = a``, ``1 < 2``) has no Łukasiewicz degree: the evaluator refuses it,
  and a decider that read it as a letter of its own would call ``a = a`` not valid (a letter can
  be 0.5). The deciders refuse it the same way.
* A variable that is free in a quantified formula is a parameter (one element of the domain);
  the deciders have no assignment to choose it by and refuse the formula by name instead of
  reading ``P(x)`` as a letter that is unrelated to ``P(a)`` and ``P(b)`` (``∀y P(y) → P(x)`` is
  Łukasiewicz-valid over {a, b}: whichever of the two ``x`` is, ``min(P(a), P(b)) ≤ P(x)``).
* The model of ``fuzzy_get_model`` reports the degree of the formula under the key ``'degree'``,
  so an atom of that name would be one key for two meanings and is refused.
"""

import pytest

from unicode_fol_kit import MSFLParser, fuzzy_evaluate, fuzzy_get_model, fuzzy_is_satisfiable, fuzzy_is_valid
from unicode_fol_kit.atp.z3_fuzzy import degree_expr
from unicode_fol_kit.fol.nodes import Atom, LukImplication, WeakConjunction, LukNegation

FL = MSFLParser(fuzzy=True)
DOMAIN = {"a", "b"}


DECIDERS = {
    "fuzzy_is_valid": lambda f: fuzzy_is_valid(f),
    "fuzzy_is_satisfiable": lambda f: fuzzy_is_satisfiable(f),
    "fuzzy_get_model": lambda f: fuzzy_get_model(f, threshold=0.5),
    "degree_expr": lambda f: degree_expr(f),
}


@pytest.mark.parametrize("decider", list(DECIDERS))
@pytest.mark.parametrize("text", ["a = a", "1 < 2", "a ≠ b", "a ≤ 1", "P(a) ⊗ (a = a)"])
def test_a_comparison_atom_is_refused_by_the_deciders_as_by_the_evaluator(decider, text):
    formula = FL.parse(text)
    with pytest.raises(TypeError, match="Comparison atom"):
        fuzzy_evaluate(formula, {"P(a)": 0.5})
    with pytest.raises(TypeError, match="Comparison atom"):
        DECIDERS[decider](formula)


def test_the_refusal_of_a_comparison_atom_names_the_atom_and_the_decider():
    with pytest.raises(TypeError) as info:
        fuzzy_is_valid(FL.parse("a = a"))
    assert "'a = a'" in str(info.value) and "decider" in str(info.value)


def test_a_formula_without_a_comparison_is_still_decided():
    assert fuzzy_is_valid(FL.parse("P → P")) is True
    assert fuzzy_is_valid(FL.parse("P")) is False
    assert fuzzy_is_satisfiable(FL.parse("P ⊗ P"), threshold=1.0) is True


@pytest.mark.parametrize("decider", ["fuzzy_is_valid", "fuzzy_is_satisfiable", "fuzzy_get_model", "degree_expr"])
@pytest.mark.parametrize("text", ["∀y P(y) → P(x)", "P(x) → ∃y P(y)", "(P(x) ⊗ Q(y)) → ∀z (P(z) ⊗ Q(z))"])
def test_a_free_variable_next_to_a_quantifier_is_refused_by_name(decider, text):
    formula = FL.parse(text)
    with pytest.raises(NotImplementedError, match="free in a quantified formula"):
        if decider == "degree_expr":
            degree_expr(formula, domain=DOMAIN)
        else:
            kwargs = {"domain": DOMAIN}
            {"fuzzy_is_valid": fuzzy_is_valid,
             "fuzzy_is_satisfiable": fuzzy_is_satisfiable,
             "fuzzy_get_model": fuzzy_get_model}[decider](formula, **kwargs)


def test_a_quantified_formula_without_a_free_variable_is_still_decided():
    # ∀y (P(y) → P(y)) over {a, b}: both instances have degree 1
    assert fuzzy_is_valid(FL.parse("∀y (P(y) → P(y))"), domain=DOMAIN) is True
    # the quantified contraction from the guide: Goedel-valid, Lukasiewicz-invalid
    q = FL.parse("∀x (P(x) → (P(x) ⊗ P(x)))")
    assert fuzzy_is_valid(q, domain=DOMAIN, tnorm="godel") is True
    assert fuzzy_is_valid(q, domain=DOMAIN, tnorm="lukasiewicz") is False


def test_a_free_variable_without_a_quantifier_is_a_letter_of_its_own():
    # P(x) → P(x) has degree 1; P(x) → P(a) does not (P(x) = 1, P(a) = 0): the domain says nothing
    # about x where there is no quantifier
    assert fuzzy_is_valid(FL.parse("P(x) → P(x)"), domain=DOMAIN) is True
    assert fuzzy_is_valid(FL.parse("P(x) → P(a)"), domain=DOMAIN) is False


def test_an_atom_named_degree_is_refused_by_the_model_and_decided_otherwise():
    degree = Atom("degree", [])
    formula = WeakConjunction(degree, LukNegation(degree))
    with pytest.raises(NotImplementedError, match="'degree'"):
        fuzzy_get_model(formula, threshold=0.5)
    # min(d, 1 - d) is at most 0.5 and reaches it at d = 0.5: the deciders are not affected
    assert fuzzy_is_satisfiable(formula, threshold=0.5) is True
    assert fuzzy_is_satisfiable(formula, threshold=0.6) is False
    other = LukImplication(Atom("Q", []), Atom("Q", []))
    assert fuzzy_get_model(other, threshold=1.0)["degree"] == 1.0
