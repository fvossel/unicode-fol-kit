"""Two bounds say what they are and can be moved where their message says.

* The matrix deciders bound their enumeration by ``manyvalued.MAX_MODELS``, and their message tells the caller
  to raise ``manyvalued.MAX_MODELS``. Four atoms over the three values of K3 are ``3**4 = 81`` assignments:
  with the bound set to 20 the decision is refused, with the bound at 81 it is made. The matrix module used
  to read a copy of the bound taken when it was imported, so setting the documented name changed nothing.
* ``int_prove`` counts its steps. Dyckhoff's G4ip terminates on every sequent, but the number of steps is
  exponential in the nesting of implications, so a sequent can need more than the budget. ``P → (Q → P)``
  takes two steps (the sequent, and the sequent the implication on the right leaves), so a budget of one step
  is spent on it. The error then says that the budget was spent and nothing was decided; it used to say that
  this was unreachable and a bug to report.
"""

import pytest

from unicode_logic_kit.atp import lj
from unicode_logic_kit.fol.nodes import And, Atom, Implies
from unicode_logic_kit.semantics import manyvalued
from unicode_logic_kit.semantics.matrix import K3_MATRIX, matrix_is_valid

A, B, C, D = (Atom(name, []) for name in "ABCD")
FOUR_ATOMS = Implies(And(And(A, B), And(C, D)), A)


def test_the_matrix_deciders_read_the_bound_the_message_names(monkeypatch):
    monkeypatch.setattr(manyvalued, "MAX_MODELS", 20)
    with pytest.raises(ValueError, match=r"3\*\*4 = 81 assignments, above MAX_MODELS = 20"):
        matrix_is_valid(FOUR_ATOMS, K3_MATRIX)
    with pytest.raises(ValueError, match=r"MAX_MODELS"):
        manyvalued.is_valid(FOUR_ATOMS, "K3")


def test_at_the_bound_the_decision_is_made(monkeypatch):
    monkeypatch.setattr(manyvalued, "MAX_MODELS", 81)
    # K3 has no valid formula: with every atom at the middle value the implication is not designated
    assert matrix_is_valid(FOUR_ATOMS, K3_MATRIX) is False


def test_a_spent_step_budget_says_that_nothing_was_decided(monkeypatch):
    monkeypatch.setattr(lj, "_MAX_STEPS", 1)
    P, Q = Atom("P", []), Atom("Q", [])
    with pytest.raises(RuntimeError) as raised:
        lj.int_prove([], Implies(P, Implies(Q, P)))
    message = str(raised.value)
    assert message.startswith("int_prove: internal step budget exceeded (1 steps).")
    assert "nothing was decided" in message
    assert "unreachable" not in message and "report a bug" not in message


def test_within_the_budget_the_sequent_is_decided():
    P, Q = Atom("P", []), Atom("Q", [])
    assert lj.int_prove([], Implies(P, Implies(Q, P))) is True
