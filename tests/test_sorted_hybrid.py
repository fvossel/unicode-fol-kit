"""A sorted constant is an element of its sort at every world, on the hybrid (standard translation) routes.

The reading: ONE universe, a sort ``S`` is the extension of the unary predicate of its name, ``c:S`` denotes
an element of ``S``, and a constant is a rigid designator, so the membership holds at EVERY world and is not
guarded by existence. The standard translation writes an atom ``S(c)`` as ``S(c, w)``; the fact
``∀w S(c, w)`` is one of ``frame_axioms`` of the formula. Expectations, in frame K, derived by hand:

* ``Human(carl:Human)`` is VALID (carl is a Human at the world it is evaluated at), and so are
  ``□Human(carl:Human)`` (at every successor too) and ``Mortal(carl:Human) → Human(carl:Human)``.
* ``◇Human(carl:Human)`` is NOT valid: K is not serial, a world without a successor falsifies ``◇``.
* ``Human(carl)`` is NOT valid: with a PLAIN carl nothing makes it a Human (one world, Human = {}).
* ``¬Human(carl:Human)`` is NOT valid: it is false at every world, carl being a Human there.
  ``□¬Human(carl:Human)`` is NOT valid either: at a world with a successor carl is a Human there too, so
  the box is false.
* ``Mortal(carl:Human) → Mortal(carl)`` and its converse are VALID: one constant, whatever it is annotated with.
* A temporal or deontic operator brings its frame axioms with it: ``Ⓖφ → φ`` (the temporal relation is
  reflexive) and ``Ⓞφ → Ⓟφ`` (the deontic relation is serial) are valid.
"""

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.hybrid_down import down_decide
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, get_backend
from unicode_fol_kit.fol.modal_translation import down_is_valid, frame_axioms, hybrid_is_valid
from unicode_fol_kit.fol.nodes import (
    Always, And, Atom, Box, Constant, Diamond, Implies, Obligatory, Permitted, Not, SortedConstant,
)

CARL_H = SortedConstant("carl", "Human")
CARL = Constant("carl")


def human(term):
    return Atom("Human", [term])


def mortal(term):
    return Atom("Mortal", [term])


# name -> (formula, valid in K by hand)
FORMULAS = {
    "Human(carl:Human)": (human(CARL_H), True),
    "□Human(carl:Human)": (Box(human(CARL_H)), True),
    "Mortal(carl:Human) → Human(carl:Human)": (Implies(mortal(CARL_H), human(CARL_H)), True),
    "□(Mortal(carl:Human) → Human(carl:Human))": (Box(Implies(mortal(CARL_H), human(CARL_H))), True),
    "Mortal(carl:Human) → Mortal(carl)": (Implies(mortal(CARL_H), mortal(CARL)), True),
    "Mortal(carl) → Mortal(carl:Human)": (Implies(mortal(CARL), mortal(CARL_H)), True),
    "◇Human(carl:Human)": (Diamond(human(CARL_H)), False),
    "Human(carl)": (human(CARL), False),
    "¬Human(carl:Human)": (Not(human(CARL_H)), False),
    "□¬Human(carl:Human)": (Box(Not(human(CARL_H))), False),
}


@pytest.mark.parametrize("name", sorted(FORMULAS))
def test_hybrid_is_valid_reads_the_membership(name):
    formula, valid = FORMULAS[name]
    assert hybrid_is_valid(formula, timeout=20000) is valid


@pytest.mark.parametrize("name", sorted(FORMULAS))
def test_the_hybrid_backend_answers_as_the_definition_says(name):
    # it used to REFUTE the valid ones: a model in which carl is no Human
    formula, valid = FORMULAS[name]
    verdict = api.prove(formula, [], backends=["hybrid"], logic="hybrid", timeout=20000)
    assert verdict.status == (PROVED if valid else REFUTED)


@pytest.mark.parametrize("name", sorted(FORMULAS))
def test_down_is_valid_proves_the_valid_ones_and_never_refutes(name):
    formula, valid = FORMULAS[name]
    verdict = down_is_valid(formula, timeout=20000)
    assert verdict.status == (PROVED if valid else UNKNOWN)


@pytest.mark.parametrize("name", sorted(FORMULAS))
def test_down_decide_agrees(name):
    formula, valid = FORMULAS[name]
    verdict = down_decide(formula, timeout=20000)
    assert verdict.status == (PROVED if valid else REFUTED)


def test_a_premise_is_a_local_premise_with_its_own_membership():
    # Mortal(carl:Human) ⊢ Human(carl:Human) is the implication of the table: valid
    verdict = api.prove(human(CARL_H), [mortal(CARL_H)], backends=["hybrid"], logic="hybrid")
    assert verdict.status == PROVED
    # carl is an Animal in the premise; nothing makes it a Human
    verdict = api.prove(human(CARL), [mortal(SortedConstant("carl", "Animal"))], backends=["hybrid"],
                        logic="hybrid")
    assert verdict.status == REFUTED
    # but one constant is one constant: a Human in the premise is a Human in the goal
    verdict = api.prove(human(CARL), [mortal(CARL_H)], backends=["hybrid"], logic="hybrid")
    assert verdict.status == PROVED


def test_frame_axioms_state_the_membership_in_the_translations_vocabulary():
    # one axiom per distinct sorted constant, the world as last argument, unguarded
    formula = Box(And(Atom("P", [SortedConstant("carl", "A")]), Atom("Q", [SortedConstant("carl", "B")])))
    assert [a.to_unicode_str() for a in frame_axioms(formula)] == [
        "∀v0 A(carl, v0)", "∀v0 B(carl, v0)"]
    assert frame_axioms(Box(Atom("P", [CARL]))) == []          # nothing without a sorted constant


def test_a_sort_named_like_the_accessibility_relation_is_kept_apart():
    # the sort R, the predicate R(carl:R): the translation writes the user predicate as R· (the relation
    # keeps R), and the membership fact must use the same name or it would be about another symbol
    formula = Atom("R", [SortedConstant("carl", "R")])
    assert hybrid_is_valid(formula, timeout=20000) is True
    assert [a.to_unicode_str() for a in frame_axioms(formula)] == ["∀v0 R·(carl, v0)"]


def test_the_hybrid_backend_gives_the_frame_axioms_of_every_relation_the_goal_mentions():
    # it used to REFUTE both, which hybrid_is_valid proves: it asked for the axioms of R only
    p = Atom("P", [])
    for formula in (Implies(Always(p), p), Implies(Obligatory(p), Permitted(p))):
        assert hybrid_is_valid(formula, timeout=20000) is True
        assert api.prove(formula, [], backends=["hybrid"], logic="hybrid",
                         timeout=20000).status == PROVED
    # and it still refutes what the frame does not give: ◇P → □P is not valid in K
    assert api.prove(Implies(Diamond(p), Box(p)), [], backends=["hybrid"], logic="hybrid",
                     timeout=20000).status == REFUTED


def test_a_sorted_quantifier_stays_refused_by_name():
    from unicode_fol_kit.fol.nodes import SortedQuantifier, Variable
    x = Variable("x")
    formula = SortedQuantifier("∀", x, "Human", Atom("Mortal", [x]))
    with pytest.raises(NotImplementedError, match="SortedQuantifier"):
        hybrid_is_valid(formula)
    verdict = get_backend("hybrid").decide(formula)
    assert verdict.status == UNKNOWN and verdict.reason == "unsupported"
