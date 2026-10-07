"""``minimal_model_size`` reads a free variable as a parameter, not as a universal.

A free variable is one unknown element, the same wherever it occurs, and a model the search
finds interprets it as the constant of its name. So ``P(x) ∧ ¬P(y)`` has a model with two
elements (``x`` one of them, ``y`` the other, ``P`` holding of ``x`` only), while the universal
closure ``∀x ∀y (P(x) ∧ ¬P(y))`` has none: taking ``y = x`` asks ``P`` to hold and fail of one
element.
"""

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.eval import minimal_model_size

parse = MSFLParser().parse


def test_two_free_variables_are_two_parameters_and_the_model_has_two_elements():
    result = minimal_model_size(parse("P(x) ∧ ¬P(y)"), max_size=3)
    assert result.size == 2
    model = result.model
    x_element, y_element = model.constants["x"], model.constants["y"]
    assert x_element != y_element
    assert (x_element,) in model.predicates[("P", 1)]
    assert (y_element,) not in model.predicates[("P", 1)]


def test_the_universal_closure_of_the_same_formula_has_no_small_model():
    result = minimal_model_size(parse("∀x ∀y (P(x) ∧ ¬P(y))"), max_size=3)
    assert result.size is None and result.exhausted


def test_one_free_variable_needs_one_element():
    result = minimal_model_size(parse("P(x)"), max_size=3)
    assert result.size == 1
    assert result.model.constants["x"] in result.model.domain
