"""A binder is renamed when its NAME meets a free variable that is substituted under it.

``Variable("y")`` (a logical variable) and ``LambdaVar("y")`` (a lambda parameter) are two nodes, but the
text has one name for both: under ``λy.`` every ``y`` reads as the parameter. Reducing

    (λx. λy. R(x, y))(y)

puts the free ``y`` of the argument under ``λy``. By hand the normal form is ``λy'. R(y, y')`` for a fresh
``y'``: the first argument is the free ``y``, the second the parameter. The reduction used to leave the
parameter as it was, and the result printed ``λy. R(y, y)``, which reads back as the term whose two arguments
are both the parameter: another term. The first name of the shape ``y<digits>`` that the term and the argument
do not use is ``y0``.

The mirror image is a quantifier's variable against a free lambda parameter of the replacement:
``∀y R(x, y)`` under ``x := λ-parameter y`` is ``∀y0 R(y, y0)``.
"""

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.fol.nodes import (
    Atom, Lambda, LambdaVar, Quantifier, Variable, beta_reduce, free_variables, substitute,
)

PARSER = MSFLParser()


def test_the_parameter_is_renamed_away_from_the_free_variable_of_the_argument():
    reduced = beta_reduce(PARSER.parse("(λx. λy. R(x, y))(y)"))
    assert reduced == Lambda(LambdaVar("y0"), Atom("R", [Variable("y"), LambdaVar("y0")]))
    assert free_variables(reduced) == {Variable("y")}


def test_the_normal_form_prints_text_that_reads_back_as_itself():
    reduced = beta_reduce(PARSER.parse("(λx. λy. R(x, y))(y)"))
    assert reduced.to_unicode_str() == "λy0. R(y, y0)"
    assert PARSER.parse(reduced.to_unicode_str()) == reduced


def test_a_name_the_term_already_uses_is_not_taken_for_the_parameter():
    # y0 is a parameter of the term, so the renamed y becomes y1
    reduced = beta_reduce(PARSER.parse("(λx. λy. λy0. S(x, y, y0))(y)"))
    assert reduced.to_unicode_str() == "λy1. λy0. S(y, y1, y0)"
    assert PARSER.parse(reduced.to_unicode_str()) == reduced


def test_an_argument_with_another_name_renames_nothing():
    reduced = beta_reduce(PARSER.parse("(λx. λy. R(x, y))(z)"))
    assert reduced == Lambda(LambdaVar("y"), Atom("R", [Variable("z"), LambdaVar("y")]))


def test_a_quantifier_is_renamed_away_from_a_free_lambda_parameter_of_the_replacement():
    x, y = Variable("x"), Variable("y")
    body = Quantifier("∀", y, Atom("R", [x, y]))
    assert substitute(body, x, LambdaVar("y")) == Quantifier(
        "∀", Variable("y0"), Atom("R", [LambdaVar("y"), Variable("y0")]))
    # the same substitution with a logical variable was already renamed, and still is
    assert substitute(body, x, Variable("y")) == Quantifier(
        "∀", Variable("y0"), Atom("R", [Variable("y"), Variable("y0")]))
