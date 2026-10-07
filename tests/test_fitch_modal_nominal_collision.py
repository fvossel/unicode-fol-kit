r"""The modal line checker of the Fitch module and a user constant spelled like a nominal's world constant.

The standard translation reads a nominal ``a`` (a ``Nominal``, or the label of ``@a``) as the reserved
world constant ``nom_a``. A USER constant spelled ``nom_a`` would be one symbol with it in Z3, so the
translation refuses a formula that holds both. The checker translates the line and each open assumption
one by one but asks one question about all of them: does the conjunction of the assumptions' images
entail the line's image? The refusal has to look at all of them together; looked at one by one, a
nominal in an assumption and a user constant in the line each pass, and Z3 then reads them as one.

By hand, with the nominals ``a`` and ``b`` and two USER constants ``nom_a`` and ``nom_b``:

* ``@a b ⊢ Q(nom_a) ↔ Q(nom_b)`` is not a local consequence in any of K, T, S4, S5: take ONE world
  ``0`` where the nominals ``a`` and ``b`` both name ``0`` (so ``@a b`` holds), and two objects
  ``nom_a`` and ``nom_b`` with ``Q`` true of the first and false of the second at ``0``. A nominal
  names a world; a constant names an object, so the first premise says nothing about the objects.
* ``Q(nom_a) ∧ ¬Q(nom_b) ⊢ ¬@a b`` is not either: the same model, where the premise holds and ``@a b``
  holds too.
"""
import pytest

from unicode_logic_kit.atp.fitch import Justification, Line, Proof, _make_modal_checker, verify_proof
from unicode_logic_kit.fol.nodes import And, At, Atom, Constant, Iff, Implies, Nominal, Not

LOGICS = ["K", "T", "S4", "S5"]


def Q(name):
    return Atom("Q", [Constant(name)])


A_NAMES_B = At("a", Nominal("b"))                 # @a b : the nominals a and b name one world


def proof(premise, line, logic):
    return Proof(premises=(Line(1, premise, Justification("Premise")),),
                 steps=(Line(2, line, Justification("Modal", (1,))),), logic=logic)


@pytest.mark.parametrize("logic", LOGICS)
def test_a_nominal_in_the_premise_and_a_user_constant_in_the_line_are_refused(logic):
    result = verify_proof(proof(A_NAMES_B, Iff(Q("nom_a"), Q("nom_b")), logic))
    assert result.ok is False
    assert "nom_a" in result.error and "collide" in result.error


@pytest.mark.parametrize("logic", LOGICS)
def test_a_user_constant_in_the_premise_and_a_nominal_in_the_line_are_refused(logic):
    premise = And(Q("nom_a"), Not(Q("nom_b")))
    result = verify_proof(proof(premise, Not(A_NAMES_B), logic))
    assert result.ok is False
    assert "collide" in result.error


def test_the_refusal_survives_a_round_trip_through_the_json_form():
    original = proof(A_NAMES_B, Iff(Q("nom_a"), Q("nom_b")), "K")
    result = verify_proof(Proof.from_dict(original.to_dict()))
    assert result.ok is False
    assert "collide" in result.error


def test_the_checker_names_the_user_symbols_and_the_nominals_it_refuses():
    accepted, reason = _make_modal_checker("K")([A_NAMES_B], Iff(Q("nom_a"), Q("nom_b")))
    assert accepted is False
    assert "nom_a" in reason and "nom_b" in reason and "['a', 'b']" in reason


def test_a_clash_between_two_open_assumptions_is_refused_whatever_the_line_says():
    # the clash is in the obligation: the two assumptions together hold a nominal a and a user
    # constant nom_a, though neither does alone and the line is about neither
    accepted, reason = _make_modal_checker("K")(
        [At("a", Atom("P", [])), Q("nom_a")], Atom("P", []))
    assert accepted is False
    assert "collide" in reason


def test_a_clash_inside_one_formula_is_still_refused():
    accepted, reason = _make_modal_checker("K")([And(Q("nom_a"), A_NAMES_B)], Q("nom_a"))
    assert accepted is False
    assert "collide" in reason


def test_a_clash_inside_one_formula_is_a_refusal_not_an_exception_of_the_proof_checkers():
    from unicode_logic_kit.atp.fitch import check_proof
    clashing = proof(And(Q("nom_a"), A_NAMES_B), Q("nom_a"), "K")
    result = verify_proof(clashing)
    assert result.ok is False
    assert "nom_a" in result.error and "collide" in result.error
    assert check_proof(clashing) is False


def test_user_constants_spelled_alike_in_two_formulas_are_one_symbol_as_before():
    # no nominal anywhere: Q(nom_a) ⊢ Q(nom_a) is trivially valid, and so is the step
    accepted, reason = _make_modal_checker("K")([Q("nom_a")], Q("nom_a"))
    assert accepted is True, reason


def test_ordinary_constants_in_the_same_shape_are_not_a_consequence():
    # the control: with names that are no world constant the step is simply not valid, because two
    # different objects may differ in Q
    accepted, reason = _make_modal_checker("K")([A_NAMES_B], Iff(Q("cc"), Q("dd")))
    assert accepted is False
    assert "not a local K-modal consequence" in reason


@pytest.mark.parametrize("logic", LOGICS)
def test_nominals_alone_still_certify_what_they_entail(logic):
    # @a b ⊢ @b a: identity of worlds is symmetric. (a nominal and no user constant: no clash)
    result = verify_proof(proof(A_NAMES_B, At("b", Nominal("a")), logic))
    assert result.ok is True, result.error


def test_a_user_constant_next_to_a_differently_named_nominal_is_no_clash():
    # nom_c is no world constant of the nominals a, b (those are nom_a, nom_b)
    accepted, reason = _make_modal_checker("K")([A_NAMES_B, Q("nom_c")], Implies(A_NAMES_B, Q("nom_c")))
    assert accepted is True, reason
