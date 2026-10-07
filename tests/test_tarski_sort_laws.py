"""The evaluator refuses a structure that is not a structure of the many-sorted definition.

THE DEFINITION. There is ONE domain. A sort ``S`` is a NON-EMPTY subset of it and is the
extension of the unary predicate ``S`` (the sort and the predicate of that name are one
symbol). A sorted constant ``c:S`` denotes an element of ``S``. An unsorted constant, an
unsorted variable and the value of a function may be any element of the domain.

``tarski.satisfies`` / ``models`` evaluate a formula in a SUPPLIED structure. A structure that
breaks one of those laws is not a structure of the definition, and a truth value in it would
answer a question nobody asked, so evaluating in it is an ``IllegalStructureError`` that names
the law and the symbols. Every structure below is built by hand, and the expectation is worked
out in the test that states it.
"""

import pytest

from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Implies, Not, Number, Quantifier, SortedConstant, SortedCount,
    SortedQuantifier, Variable,
)
from unicode_logic_kit.semantics import tarski
from unicode_logic_kit.semantics.tarski import IllegalStructureError, Structure, models, satisfies

X = Variable("x")


def _sorted_world(**overrides):
    """domain {0,1,2}; S = {0,1}; carl = 0; P = {1}. A structure of the definition."""
    arguments = dict(domain=[0, 1, 2], constants={"carl": 0}, sorts={"S": [0, 1]},
                     predicates={("P", 1): {(1,)}})
    arguments.update(overrides)
    return Structure(**arguments)


def test_a_legal_sorted_structure_is_evaluated_and_passes_the_check():
    world = _sorted_world()
    formula = And(Atom("P", [SortedConstant("carl", "S")]),
                  SortedQuantifier("∃", X, "S", Atom("P", [X])))
    assert tarski.structure_violations(world, formula) == []
    tarski.check_structure(world, formula)
    # P(carl:S): carl = 0, P = {1}: false; ∃x:S P(x): x = 1: true
    assert models(Atom("P", [SortedConstant("carl", "S")]), world) is False
    assert models(SortedQuantifier("∃", X, "S", Atom("P", [X])), world) is True


def test_a_sorted_constant_outside_its_sort_is_an_error_not_a_truth_value():
    """carl = 2 but S = {0,1}: carl:S denotes an element of S, so this structure is not one."""
    world = _sorted_world(constants={"carl": 2})
    for formula in (Atom("P", [SortedConstant("carl", "S")]),
                    SortedQuantifier("∃", X, "S", Atom("=", [X, SortedConstant("carl", "S")])),
                    Not(Atom("P", [SortedConstant("carl", "S")]))):
        with pytest.raises(IllegalStructureError, match=r"carl:S.*2.*not in the sort 'S'"):
            models(formula, world)
        with pytest.raises(IllegalStructureError, match=r"carl:S"):
            tarski.check_structure(world, formula)
    # the illegal annotation, not the constant: the plain constant of that name may be anywhere
    assert models(Atom("P", [Constant("carl")]), world) is False


def test_the_error_names_every_violation_the_up_front_check_finds():
    world = Structure(domain=[0, 1, 2], constants={"carl": 2},
                      sorts={"S": [0, 1], "Empty": [], "Wild": [0, 9]})
    formula = And(Atom("P", [SortedConstant("carl", "S")]),
                  SortedQuantifier("∀", X, "Undeclared", Atom("P", [X])))
    problems = tarski.structure_violations(world, formula)
    assert any("'Empty' is empty" in p for p in problems)
    assert any("'Wild' holds [9]" in p and "not in the domain" in p for p in problems)
    assert any("carl:S denotes 2" in p for p in problems)
    assert any("'Undeclared'" in p and "does not declare" in p for p in problems)
    with pytest.raises(IllegalStructureError) as raised:
        tarski.check_structure(world, formula)
    for p in problems:
        assert p in str(raised.value)


def test_an_empty_sort_is_an_error_for_a_universal_and_for_an_existential():
    """A sort is never empty: ∀x:Nothing φ would be vacuously true in a structure that is no
    structure of the definition."""
    world = Structure(domain=[0, 1], sorts={"Nothing": []})
    for kind in ("∀", "∃"):
        with pytest.raises(IllegalStructureError, match="'Nothing' is empty"):
            models(SortedQuantifier(kind, X, "Nothing", Atom("P", [X])), world)
    for formula in (SortedCount("ge", Number(1), X, "Nothing", Atom("P", [X])),
                    Atom("Nothing", [Constant("c")])):
        with pytest.raises(IllegalStructureError, match="'Nothing' is empty"):
            satisfies(formula, Structure(domain=[0, 1], constants={"c": 0}, sorts={"Nothing": []}), {})


def test_a_sort_holding_an_element_outside_the_domain_is_an_error():
    world = Structure(domain=[0, 1], sorts={"S": [0, 7]})
    with pytest.raises(IllegalStructureError, match=r"'S' holds \[7\], which is not in the domain"):
        models(SortedQuantifier("∃", X, "S", Atom("P", [X])), world)


def test_a_name_that_is_a_sort_and_a_predicate_with_two_extensions_is_an_error():
    """S = {0,1} as a sort but {1} as a predicate: S(x) and ∀x:S would be two different sets."""
    world = Structure(domain=[0, 1, 2], constants={"c": 1}, sorts={"S": [0, 1]},
                      predicates={("S", 1): {(1,)}})
    for formula in (SortedQuantifier("∀", X, "S", Atom("=", [X, X])), Atom("S", [Constant("c")])):
        with pytest.raises(IllegalStructureError,
                           match=r"'S' is both a sort and a unary predicate.*sort holds \[0, 1\].*predicate holds \[1\]"):
            models(formula, world)
    # the same extension in both tables is the one symbol, and fine
    agreeing = Structure(domain=[0, 1, 2], constants={"c": 1}, sorts={"S": [0, 1]},
                         predicates={("S", 1): {(0,), (1,)}})
    assert models(Atom("S", [Constant("c")]), agreeing) is True
    assert models(SortedQuantifier("∀", X, "S", Atom("S", [X])), agreeing) is True


def test_an_atom_over_a_name_known_only_as_a_sort_reads_the_sort():
    """No predicate table for S: S(t) holds exactly when the value of t is in the sort S = {0,1}."""
    world = Structure(domain=[0, 1, 2], constants={"in": 0, "out": 2}, sorts={"S": [0, 1]})
    assert models(Atom("S", [Constant("in")]), world) is True
    assert models(Atom("S", [Constant("out")]), world) is False
    # as a guard: ∀x (S(x) → x ≠ out), and the sort restricted form, agree
    guarded = Quantifier("∀", X, Implies(Atom("S", [X]), Atom("≠", [X, Constant("out")])))
    assert models(guarded, world) is True
    assert models(SortedQuantifier("∃", X, "S", Atom("=", [X, Constant("out")])), world) is False
    # a binary predicate of that name is another symbol: no table, empty
    assert models(Atom("S", [Constant("in"), Constant("in")]), world) is False


def test_a_sorted_constant_of_an_undeclared_sort_is_a_key_error_like_a_sorted_quantifier():
    world = Structure(domain=[0], constants={"c": 0})
    with pytest.raises(KeyError, match="'Nowhere'"):
        models(Atom("P", [SortedConstant("c", "Nowhere")]), world)
    with pytest.raises(KeyError, match="'Nowhere'"):
        models(SortedQuantifier("∀", X, "Nowhere", Atom("P", [X])), world)


def test_the_evaluator_checks_what_it_reads_and_the_up_front_check_checks_everything():
    """Documented: ``satisfies`` raises where it reads an illegal sort or constant. A conjunct whose
    first operand is false is never read, so the evaluation returns False; ``check_structure`` on the
    formula still refuses the structure."""
    world = _sorted_world(constants={"carl": 2})
    formula = And(Atom("P", [Constant("carl")]), Atom("P", [SortedConstant("carl", "S")]))
    assert models(formula, world) is False          # P(carl) is false (carl = 2, P = {1}): the rest is not read
    with pytest.raises(IllegalStructureError, match="carl:S"):
        tarski.check_structure(world, formula)


def test_a_structure_replaced_after_a_first_read_is_checked_again():
    """The laws on a sort are verified when it is first read and again when its table is replaced."""
    world = _sorted_world()
    sentence = SortedQuantifier("∃", X, "S", Atom("P", [X]))
    assert models(sentence, world) is True
    world.sorts["S"] = ()                            # a replaced table
    with pytest.raises(IllegalStructureError, match="'S' is empty"):
        models(sentence, world)
