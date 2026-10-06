"""The THF writers for modal and free logic and a free variable.

A free variable is a parameter: one unknown individual. THF has no free variables, so a writer has to say what
the variable stands for.

* ``hol.thf_modal.to_thf_modal_full`` binds it in front of the whole conjecture, as ``fol.qml.to_thf_modal``
  does: for a conjecture that stands alone, "valid for the parameter" and "valid for every individual" are one
  thing. Under an actualist regime (``varying``, ``increasing``, ``decreasing``) the individual exists at the
  world of evaluation, which is the guard ``existsAt @ X`` in front of the lifted formula. By hand, for
  ``□P(x) → P(x)``:

      constant:  ! [X: $i] : ( mvalid @ ( mimplies @ ( mbox @ ( p @ X ) ) @ ( p @ X ) ) )
      varying:   ! [X: $i] : ( mvalid @ ( mimplies @ ( existsAt @ X ) @ ( mimplies @ ( mbox @ ( p @ X ) ) @ ( p @ X ) ) ) )

  The conjecture used to carry ``X`` with no binder at all.
* ``hol.free.to_thf_free`` closes a conjecture universally under the existence guard (the parameter exists),
  and refuses an ASSERTED formula with a free variable by name: ``∀x P(x)`` says more than ``P(x)``.
"""

import re

import pytest

from unicode_fol_kit.fol._modal_nodes import Box
from unicode_fol_kit.fol.nodes import Atom, Constant, Implies, Quantifier, Variable
from unicode_fol_kit.fol.qml import to_thf_modal
from unicode_fol_kit.hol.free import to_thf_free
from unicode_fol_kit.hol.thf_modal import to_thf_modal_full

X, Y = Variable("x"), Variable("y")
OPEN = Implies(Box(Atom("P", [X])), Atom("P", [X]))
TWO = Implies(Box(Atom("R", [X, Y])), Atom("R", [X, Y]))
CLOSED = Quantifier("∀", X, OPEN)
GROUND = Implies(Box(Atom("P", [Constant("alice")])), Atom("P", [Constant("alice")]))
MODES = ["constant", "possibilist", "varying", "increasing", "decreasing"]


def goal(text):
    [line] = [line for line in text.splitlines() if line.startswith("thf(goal")]
    return line


def unbound_variables(line):
    """The THF variables (upper-case words) of ``line`` that no ``[... : type]`` binder of it declares."""
    bound = set(re.findall(r"[\[,]\s*([A-Z][A-Za-z0-9_]*)\s*:", line))
    used = set(re.findall(r"(?<![A-Za-z0-9_$])([A-Z][A-Za-z0-9_]*)", line))
    return used - bound


def test_the_parameter_is_bound_in_front_of_the_conjecture_under_a_constant_domain():
    assert goal(to_thf_modal_full(OPEN, mode="constant")) == (
        "thf(goal, conjecture, ( ! [X: $i] : ( mvalid @ ( mimplies @ ( mbox @ ( p @ X ) ) @ ( p @ X ) ) ) )).")


def test_the_parameter_exists_at_the_world_of_evaluation_under_a_varying_domain():
    assert goal(to_thf_modal_full(OPEN, mode="varying")) == (
        "thf(goal, conjecture, ( ! [X: $i] : ( mvalid @ ( mimplies @ ( existsAt @ X ) @ "
        "( mimplies @ ( mbox @ ( p @ X ) ) @ ( p @ X ) ) ) ) )).")


@pytest.mark.parametrize("mode", MODES)
@pytest.mark.parametrize("formula", [OPEN, TWO, CLOSED, GROUND], ids=["open", "two", "closed", "ground"])
def test_no_variable_of_the_conjecture_is_left_without_a_binder(formula, mode):
    assert unbound_variables(goal(to_thf_modal_full(formula, mode=mode))) == set()


@pytest.mark.parametrize("mode", MODES)
@pytest.mark.parametrize("formula", [OPEN, TWO, CLOSED, GROUND], ids=["open", "two", "closed", "ground"])
def test_the_two_modal_writers_write_one_conjecture(formula, mode):
    # the alethic fragment is the part the two writers share, and their conjectures are the same text there
    assert goal(to_thf_modal_full(formula, mode=mode)) == goal(to_thf_modal(formula, mode=mode))


@pytest.mark.parametrize("mode", MODES)
def test_a_formula_without_a_free_variable_is_written_as_before(mode):
    assert goal(to_thf_modal_full(CLOSED, mode=mode)) == (
        "thf(goal, conjecture, ( mvalid @ ( mforall @ ( ^ [X: $i] : "
        "( mimplies @ ( mbox @ ( p @ X ) ) @ ( p @ X ) ) ) ) )).")


def test_the_free_logic_writer_refuses_an_asserted_formula_with_a_free_variable():
    with pytest.raises(NotImplementedError, match=r"to_thf_free: the asserted formula \(conjecture=False\) has the free variable 'x'"):
        to_thf_free(Atom("P", [X]), conjecture=False)


def test_the_free_logic_writer_still_writes_the_conjecture_and_a_closed_axiom():
    closed_under_the_guard = "( ! [X: $i] : ( ( existsBang @ X ) => ( ( denotes @ X ) & ( p @ X ) ) ) )"
    assert goal(to_thf_free(Atom("P", [X]))) == f"thf(goal, conjecture, {closed_under_the_guard})."
    assert goal(to_thf_free(Quantifier("∀", X, Atom("P", [X])), conjecture=False)) == (
        f"thf(goal, axiom, {closed_under_the_guard}).")
