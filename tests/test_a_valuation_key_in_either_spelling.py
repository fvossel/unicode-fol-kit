"""A valuation keyed by the text of an atom as a formula is read like one keyed by its key.

The guide taught "the key of an atom is ``atom.to_unicode_str()``". For a hand-built atom over
``Constant("a")`` and ``Constant("b")`` that text is ``Likes('a', 'b')`` now, because the bare
``a`` would read as a variable and a formula writes the constant in quotes; the KEY of the same
atom, with every constant written by its bare name, is ``Likes(a, b)``. An evaluator that looked
the atom up under the key alone would find nothing in a valuation built the way the guide said,
and the Kripke evaluator reads a missing key as false without a word.

So every evaluator that reads a valuation, model or trace from its caller looks an atom up under
its key and then under its text as a formula (``find_key``). Every expected value below is worked
out by hand from the semantics and written as a literal. Each family gets

* the idiom of the guide: a hand-built atom, a valuation keyed by ``atom.to_unicode_str()``
  (the test first asserts that this text holds the quotes), and a formula that is true only if
  the key is found,
* the same valuation keyed by ``atom_key`` and typed by hand,
* a quantified formula over the domain ``{"a", "b"}`` with one key of each spelling,
* a control with the lookup replaced by the plain bare-name lookup, which shows what the
  function is for: the valuation keyed by the text then gives the wrong answer.

A mapping that holds both spellings of one atom with different values is refused, and one that
holds them with equal values is read. A key that holds a complete quoted constant (the key of
an atom whose names hold apostrophes) is refused where it is made, because it is the second
spelling of another atom's key; a name that merely holds an apostrophe keeps its key.
"""

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.ltl_tableau import LTLTrace, ltl_trace_satisfies
from unicode_logic_kit.fol import _atom_keys as atom_keys_module
from unicode_logic_kit.fol._atom_keys import (
    AtomKeys, atom_key, find_key, find_own_key, other_key)
from unicode_logic_kit.fol._fol_nodes import Node
from unicode_logic_kit.fol._msfl_nodes import key_text
from unicode_logic_kit.fol.nodes import (
    Atom, Box, Constant, Diamond, Function, Not, SortedConstant, Variable, Would)
from unicode_logic_kit.semantics import conditional as conditional_module
from unicode_logic_kit.semantics import fuzzy_kripke as fuzzy_kripke_module
from unicode_logic_kit.semantics import intuitionistic as intuitionistic_module
from unicode_logic_kit.semantics import kripke as kripke_module
from unicode_logic_kit.semantics.conditional import CounterfactualModel, cf_satisfies
from unicode_logic_kit.semantics.fuzzy import evaluate as fuzzy_evaluate
from unicode_logic_kit.semantics.fuzzy_kripke import FuzzyKripkeModel, satisfies_fuzzy_modal
from unicode_logic_kit.semantics.intuitionistic import IntKripkeModel
from unicode_logic_kit.semantics.kripke import (
    KripkeModel, satisfies_modal, sorted_constant_violations)
from unicode_logic_kit.semantics.manyvalued import kleene_value
from unicode_logic_kit.semantics.matrix import FDE_MATRIX, matrix_value


def parse(text, **mode):
    return MSFLParser(**mode).parse(text)


a, b = Constant("a"), Constant("b")

#: the atom of the guide, built by hand over two constants that need quotes in a formula
LIKES = Atom("Likes", [a, b])
LIKES_KEY, LIKES_TEXT = "Likes(a, b)", "Likes('a', 'b')"

FORALL_P = parse("∀x P(x)")
EXISTS_P = parse("∃x P(x)")
FUZZY_FORALL = parse("∀x P(x)", fuzzy=True)
FUZZY_EXISTS = parse("∃x P(x)", fuzzy=True)


def P(term):
    return Atom("P", [term])


def bare_lookup(keys, atom):
    """The lookup an evaluator would make if it knew only the key: the control of every family."""
    key = atom_key(atom)
    return key if key in keys else None


def bare_find(self, table, atom):
    """``AtomKeys.find`` with the second spelling taken away (the atom is still recorded)."""
    key = self.key(atom)
    return key if key in table else None


# ---------------------------------------------------------------------------
# The two spellings of the key of one atom
# ---------------------------------------------------------------------------

def test_the_guide_idiom_gives_a_text_that_holds_the_quotes():
    # the premise of every test below: the text of the atom is not its key
    assert LIKES.to_unicode_str() == LIKES_TEXT
    assert atom_key(LIKES) == LIKES_KEY


def test_the_other_spelling_of_a_key_is_the_text_of_the_formula():
    assert other_key(LIKES) == LIKES_TEXT
    # one constant in quotes is enough; a bare one is not rewritten
    assert other_key(Atom("Likes", [Constant("alice"), b])) == "Likes(alice, 'b')"
    # a sorted constant is read as the plain constant, as atom_key reads it
    assert other_key(Atom("Mortal", [SortedConstant("c", "S")])) == "Mortal('c')"
    assert atom_key(Atom("Mortal", [SortedConstant("c", "S")])) == "Mortal(c)"


def test_an_atom_with_one_spelling_has_no_other_key():
    assert other_key(Atom("Likes", [Constant("alice"), Constant("bob")])) is None
    assert other_key(Atom("P", [])) is None
    # a name with an apostrophe is not a bare word, so a formula writes it in quotes
    assert other_key(Atom("P", [Constant("D'Alembert")])) == "P('D\\'Alembert')"


def test_a_constant_without_a_text_has_no_formula_text_to_be_a_key():
    # the empty name has no text in any spelling: the atom has one key and no other
    assert other_key(Atom("P", [Constant("")])) is None
    assert find_key({"P()"}, Atom("P", [Constant("")])) == "P()"


def test_find_key_reads_either_spelling_of_a_set():
    assert find_key({LIKES_KEY}, LIKES) == LIKES_KEY
    assert find_key({LIKES_TEXT}, LIKES) == LIKES_TEXT
    assert find_key({"Likes(a, c)", "P"}, LIKES) is None
    # both spellings in a set are one atom, true: no conflict between members of a set
    assert find_key({LIKES_KEY, LIKES_TEXT}, LIKES) == LIKES_KEY


def test_find_key_reads_either_spelling_of_a_mapping():
    assert find_key({LIKES_KEY: 0.5}, LIKES) == LIKES_KEY
    assert find_key({LIKES_TEXT: 0.5}, LIKES) == LIKES_TEXT
    assert find_key({}, LIKES) is None


def test_find_key_prefers_the_key_and_accepts_two_equal_entries():
    assert find_key({LIKES_KEY: 0.5, LIKES_TEXT: 0.5}, LIKES) == LIKES_KEY
    assert find_key({LIKES_KEY: True, LIKES_TEXT: True}, LIKES) == LIKES_KEY


def test_find_key_refuses_two_entries_with_different_values():
    table = {LIKES_KEY: 0.25, LIKES_TEXT: 0.75}
    with pytest.raises(ValueError) as info:
        find_key(table, LIKES)
    message = str(info.value)
    assert "one atom, two entries" in message
    assert repr(LIKES_KEY) in message and repr(LIKES_TEXT) in message
    assert "0.25" in message and "0.75" in message


def test_an_atom_with_one_spelling_cannot_hold_two_entries():
    # nothing to conflict with: both spellings are the one string
    alice = Atom("Likes", [Constant("alice"), Constant("bob")])
    assert find_key({"Likes(alice, bob)": 1.0}, alice) == "Likes(alice, bob)"


def test_find_own_key_is_the_bare_lookup_of_a_table_the_kit_built():
    assert find_own_key({LIKES_KEY: 1}, LIKES) == LIKES_KEY
    # the text of the formula is not looked for: the table is the kit's own
    assert find_own_key({LIKES_TEXT: 1}, LIKES) is None


def test_atoms_keys_find_records_the_atom_like_key():
    keys = AtomKeys("the route")
    assert keys.find({LIKES_TEXT: 1}, LIKES) == LIKES_TEXT
    # the refusal of two different atoms with one key still works through find
    with pytest.raises(NotImplementedError) as info:
        keys.find({"P(x)": 1}, P(Variable("x")))
        keys.find({"P(x)": 1}, P(Constant("x")))
    assert "two different atoms have one key" in str(info.value)


# ---------------------------------------------------------------------------
# The Kripke evaluator
# ---------------------------------------------------------------------------

def kripke(true_keys, domain=("a", "b")):
    return KripkeModel({0}, valuation={0: set(true_keys)}, domain=set(domain))


def box_model(true_keys):
    return KripkeModel({0, 1}, relations={"alethic": {(0, 1)}}, valuation={1: set(true_keys)})


def test_kripke_a_valuation_keyed_by_the_text_of_the_formula_is_found():
    # world 1 holds the atom: the only successor of 0 satisfies it, so Box is true
    assert satisfies_modal(Box(LIKES), box_model({LIKES.to_unicode_str()}), 0) is True
    assert satisfies_modal(Diamond(LIKES), box_model({LIKES.to_unicode_str()}), 0) is True


def test_kripke_a_valuation_keyed_by_the_key_is_found():
    assert satisfies_modal(Box(LIKES), box_model({"Likes(a, b)"}), 0) is True
    # a key of another atom does not make the atom true
    assert satisfies_modal(Box(LIKES), box_model({"Likes(a, a)"}), 0) is False
    assert satisfies_modal(Box(LIKES), box_model(set()), 0) is False


def test_kripke_a_universal_over_one_key_of_each_spelling_is_true():
    # P(a) by its key and P('b') by its text: both instances of ∀x P(x) hold
    assert satisfies_modal(FORALL_P, kripke({"P(a)", "P('b')"}), 0) is True
    assert satisfies_modal(FORALL_P, kripke({"P('a')", "P(b)"}), 0) is True


def test_kripke_a_universal_with_one_instance_missing_is_false():
    # P(b) is in neither spelling, so the instance at b is false
    assert satisfies_modal(FORALL_P, kripke({"P('a')"}), 0) is False
    assert satisfies_modal(FORALL_P, kripke({"P(a)"}), 0) is False


def test_kripke_an_existential_needs_one_instance_in_either_spelling():
    assert satisfies_modal(EXISTS_P, kripke({"P('b')"}), 0) is True
    assert satisfies_modal(EXISTS_P, kripke({"Q(a)"}), 0) is False


def test_kripke_the_guard_of_a_sorted_constant_is_found_in_either_spelling():
    formula = Atom("Q", [SortedConstant("a", "Human")])
    # the guard atom is Human(a), whose text is Human('a')
    assert sorted_constant_violations(formula, KripkeModel({0}, valuation={0: {"Human('a')"}})) == []
    assert sorted_constant_violations(formula, KripkeModel({0}, valuation={0: {"Human(a)"}})) == []
    assert sorted_constant_violations(formula, KripkeModel({0})) == [("a", "Human", 0)]


def test_kripke_control_a_lookup_by_the_key_alone_reads_the_text_keyed_model_as_false(monkeypatch):
    model = box_model({LIKES.to_unicode_str()})
    assert satisfies_modal(Box(LIKES), model, 0) is True
    monkeypatch.setattr(kripke_module, "find_key", bare_lookup)
    assert satisfies_modal(Box(LIKES), model, 0) is False
    # the same lookup still finds a model keyed by the key
    assert satisfies_modal(Box(LIKES), box_model({LIKES_KEY}), 0) is True


# ---------------------------------------------------------------------------
# The fuzzy evaluator
# ---------------------------------------------------------------------------

def test_fuzzy_a_valuation_keyed_by_the_text_of_the_formula_is_found():
    assert fuzzy_evaluate(LIKES, {LIKES.to_unicode_str(): 0.25}) == 0.25


def test_fuzzy_a_valuation_keyed_by_the_key_is_found():
    assert fuzzy_evaluate(LIKES, {"Likes(a, b)": 0.75}) == 0.75


def test_fuzzy_a_quantified_formula_reads_one_key_of_each_spelling():
    valuation = {"P(a)": 0.5, "P('b')": 0.25}
    # inf and sup of {0.5, 0.25}
    assert fuzzy_evaluate(FUZZY_FORALL, valuation, domain={"a", "b"}) == 0.25
    assert fuzzy_evaluate(FUZZY_EXISTS, valuation, domain={"a", "b"}) == 0.5


def test_fuzzy_a_key_in_neither_spelling_is_named_by_its_key():
    with pytest.raises(KeyError) as info:
        fuzzy_evaluate(LIKES, {"Likes(a, c)": 0.5})
    assert "Likes(a, b)" in str(info.value)


def test_fuzzy_two_entries_for_one_atom_with_different_degrees_are_refused():
    with pytest.raises(ValueError) as info:
        fuzzy_evaluate(LIKES, {LIKES_KEY: 0.25, LIKES_TEXT: 0.75})
    assert "one atom, two entries" in str(info.value)
    # two equal degrees are one statement
    assert fuzzy_evaluate(LIKES, {LIKES_KEY: 0.25, LIKES_TEXT: 0.25}) == 0.25


def test_fuzzy_the_refusal_of_two_alike_atoms_still_holds_for_a_text_keyed_valuation():
    pair = parse("P(x) → P('x')", fuzzy=True)
    with pytest.raises(NotImplementedError) as info:
        fuzzy_evaluate(pair, {"P('x')": 1.0, "P(x)": 1.0})
    assert "two different atoms have one key" in str(info.value)


def test_fuzzy_control_a_lookup_by_the_key_alone_misses_the_text_keyed_valuation(monkeypatch):
    valuation = {LIKES.to_unicode_str(): 0.25}
    assert fuzzy_evaluate(LIKES, valuation) == 0.25
    monkeypatch.setattr(AtomKeys, "find", bare_find)
    with pytest.raises(KeyError):
        fuzzy_evaluate(LIKES, valuation)


# ---------------------------------------------------------------------------
# The three-valued evaluator
# ---------------------------------------------------------------------------

def test_manyvalued_a_valuation_keyed_by_the_text_of_the_formula_is_found():
    assert kleene_value(LIKES, {LIKES.to_unicode_str(): 0.5}) == 0.5
    assert kleene_value(Not(LIKES), {LIKES.to_unicode_str(): 1.0}) == 0.0


def test_manyvalued_a_valuation_keyed_by_the_key_is_found():
    assert kleene_value(LIKES, {"Likes(a, b)": 1.0}) == 1.0


def test_manyvalued_a_quantified_formula_reads_one_key_of_each_spelling():
    valuation = {"P('a')": 1.0, "P(b)": 0.5}
    # min and max of {1, 1/2}
    assert kleene_value(FORALL_P, valuation, domain={"a", "b"}) == 0.5
    assert kleene_value(EXISTS_P, valuation, domain={"a", "b"}) == 1.0


def test_manyvalued_two_entries_for_one_atom_with_different_values_are_refused():
    with pytest.raises(ValueError) as info:
        kleene_value(LIKES, {LIKES_KEY: 1.0, LIKES_TEXT: 0.0})
    assert "one atom, two entries" in str(info.value)
    assert kleene_value(LIKES, {LIKES_KEY: 0.5, LIKES_TEXT: 0.5}) == 0.5


def test_manyvalued_control_a_lookup_by_the_key_alone_misses_the_text_keyed_valuation(monkeypatch):
    valuation = {LIKES.to_unicode_str(): 0.5}
    assert kleene_value(LIKES, valuation) == 0.5
    monkeypatch.setattr(AtomKeys, "find", bare_find)
    with pytest.raises(KeyError):
        kleene_value(LIKES, valuation)


# ---------------------------------------------------------------------------
# The matrix evaluator
# ---------------------------------------------------------------------------

def test_matrix_a_valuation_keyed_by_the_text_of_the_formula_is_found():
    assert matrix_value(LIKES, {LIKES.to_unicode_str(): "B"}, FDE_MATRIX) == "B"


def test_matrix_a_quantified_formula_reads_one_key_of_each_spelling():
    # conj of T and B is B; disj of F and N is N, in the four-valued lattice of FDE
    assert matrix_value(FORALL_P, {"P(a)": "T", "P('b')": "B"}, FDE_MATRIX,
                        domain=("a", "b")) == "B"
    assert matrix_value(EXISTS_P, {"P('a')": "F", "P(b)": "N"}, FDE_MATRIX,
                        domain=("a", "b")) == "N"


def test_matrix_two_entries_for_one_atom_with_different_values_are_refused():
    with pytest.raises(ValueError) as info:
        matrix_value(LIKES, {LIKES_KEY: "T", LIKES_TEXT: "F"}, FDE_MATRIX)
    assert "one atom, two entries" in str(info.value)
    assert matrix_value(LIKES, {LIKES_KEY: "N", LIKES_TEXT: "N"}, FDE_MATRIX) == "N"


def test_matrix_control_a_lookup_by_the_key_alone_misses_the_text_keyed_valuation(monkeypatch):
    valuation = {LIKES.to_unicode_str(): "B"}
    assert matrix_value(LIKES, valuation, FDE_MATRIX) == "B"
    monkeypatch.setattr(AtomKeys, "find", bare_find)
    with pytest.raises(KeyError):
        matrix_value(LIKES, valuation, FDE_MATRIX)


# ---------------------------------------------------------------------------
# The intuitionistic evaluator
# ---------------------------------------------------------------------------

#: worlds 0 <= 1: the up-set of 0 is {0, 1}, that of 1 is {1}
UPSET = {0: frozenset({0, 1}), 1: frozenset({1})}


def test_intuitionistic_a_valuation_keyed_by_the_text_of_the_formula_is_found():
    model = IntKripkeModel(UPSET, {LIKES.to_unicode_str(): frozenset({1})})
    # forced at world 1 only
    assert model.forces(1, LIKES) is True
    assert model.forces(0, LIKES) is False


def test_intuitionistic_a_valuation_keyed_by_the_key_is_found():
    model = IntKripkeModel(UPSET, {"Likes(a, b)": frozenset({1})})
    assert model.forces(1, LIKES) is True
    assert model.forces(0, LIKES) is False


def test_intuitionistic_a_quantified_formula_reads_one_key_of_each_spelling():
    domains = {0: frozenset({"a", "b"}), 1: frozenset({"a", "b"})}
    both = IntKripkeModel(UPSET, {"P(a)": frozenset({0, 1}), "P('b')": frozenset({0, 1})}, domains)
    assert both.forces(0, FORALL_P) is True
    only_a = IntKripkeModel(UPSET, {"P('a')": frozenset({0, 1})}, domains)
    # P(b) is forced nowhere
    assert only_a.forces(0, FORALL_P) is False
    assert only_a.forces(0, EXISTS_P) is True


def test_intuitionistic_two_entries_with_different_worlds_are_refused():
    model = IntKripkeModel(UPSET, {LIKES_KEY: frozenset({1}), LIKES_TEXT: frozenset({0, 1})})
    with pytest.raises(ValueError) as info:
        model.forces(1, LIKES)
    assert "one atom, two entries" in str(info.value)


def test_intuitionistic_control_a_lookup_by_the_key_alone_misses_the_text_keyed_model(monkeypatch):
    model = IntKripkeModel(UPSET, {LIKES.to_unicode_str(): frozenset({1})})
    assert model.forces(1, LIKES) is True
    monkeypatch.setattr(intuitionistic_module, "find_key", bare_lookup)
    assert model.forces(1, LIKES) is False


# ---------------------------------------------------------------------------
# The counterfactual (sphere) evaluator
# ---------------------------------------------------------------------------

def sphere_model(true_keys):
    return CounterfactualModel((0,), {0: frozenset(true_keys)}, {0: [frozenset({0})]})


def test_counterfactual_a_valuation_keyed_by_the_text_of_the_formula_is_found():
    assert cf_satisfies(LIKES, sphere_model({LIKES.to_unicode_str()}), 0) is True
    assert cf_satisfies(LIKES, sphere_model({"Likes(a, a)"}), 0) is False


def test_counterfactual_a_valuation_keyed_by_the_key_is_found():
    assert cf_satisfies(LIKES, sphere_model({"Likes(a, b)"}), 0) is True


def test_counterfactual_a_conditional_reads_one_key_of_each_spelling():
    conditional = Would(P(a), P(b))
    # the one sphere {0} holds the antecedent world, where the consequent must hold
    assert cf_satisfies(conditional, sphere_model({"P(a)", "P('b')"}), 0) is True
    assert cf_satisfies(conditional, sphere_model({"P('a')"}), 0) is False


def test_counterfactual_control_a_lookup_by_the_key_alone_misses_the_text_keyed_model(monkeypatch):
    model = sphere_model({LIKES.to_unicode_str()})
    assert cf_satisfies(LIKES, model, 0) is True
    monkeypatch.setattr(conditional_module, "find_key", bare_lookup)
    assert cf_satisfies(LIKES, model, 0) is False


# ---------------------------------------------------------------------------
# The graded Kripke evaluator
# ---------------------------------------------------------------------------

def graded_model(degrees):
    return FuzzyKripkeModel({"w0", "w1"}, relations={"alethic": {("w0", "w1"): 0.5}},
                            valuation={"w1": degrees})


def test_fuzzy_kripke_a_valuation_keyed_by_the_text_of_the_formula_is_found():
    model = graded_model({LIKES.to_unicode_str(): 0.5})
    # Łukasiewicz: Box is the infimum of min(1, 1 - R + deg) over the two worlds: at w0 it is
    # min(1, 1 - 0 + 0) = 1 (no self-loop), at w1 min(1, 1 - 0.5 + 0.5) = 1; the atom at w1 is 0.5
    assert satisfies_fuzzy_modal(LIKES, model, "w1") == 0.5
    assert satisfies_fuzzy_modal(Box(LIKES), model, "w0") == 1.0


def test_fuzzy_kripke_a_valuation_keyed_by_the_key_is_found():
    assert satisfies_fuzzy_modal(LIKES, graded_model({"Likes(a, b)": 0.75}), "w1") == 0.75


def test_fuzzy_kripke_a_key_in_neither_spelling_reads_as_degree_zero():
    assert satisfies_fuzzy_modal(LIKES, graded_model({"Likes(a, a)": 0.75}), "w1") == 0.0


def test_fuzzy_kripke_two_entries_with_different_degrees_are_refused():
    model = graded_model({LIKES_KEY: 0.25, LIKES_TEXT: 0.5})
    with pytest.raises(ValueError) as info:
        satisfies_fuzzy_modal(LIKES, model, "w1")
    assert "one atom, two entries" in str(info.value)


def test_fuzzy_kripke_control_a_lookup_by_the_key_alone_misses_the_text_keyed_model(monkeypatch):
    model = graded_model({LIKES.to_unicode_str(): 0.5})
    assert satisfies_fuzzy_modal(LIKES, model, "w1") == 0.5
    monkeypatch.setattr(fuzzy_kripke_module, "find_key", bare_lookup)
    assert satisfies_fuzzy_modal(LIKES, model, "w1") == 0.0


# ---------------------------------------------------------------------------
# A trace of a linear-time formula
# ---------------------------------------------------------------------------

def test_a_trace_keyed_by_the_text_of_the_formula_is_found():
    # one position that holds the atom, then an empty cycle
    trace = LTLTrace(prefix=(frozenset({LIKES.to_unicode_str()}),), cycle=(frozenset(),))
    assert ltl_trace_satisfies(LIKES, trace, position=0) is True
    assert ltl_trace_satisfies(LIKES, trace, position=1) is False


def test_a_trace_keyed_by_the_key_is_found():
    trace = LTLTrace(prefix=(frozenset({"Likes(a, b)"}),), cycle=(frozenset(),))
    assert ltl_trace_satisfies(LIKES, trace, position=0) is True


# ---------------------------------------------------------------------------
# One rendering per lookup where the two spellings are one string
# ---------------------------------------------------------------------------

@pytest.fixture
def renderings(monkeypatch):
    """Count the renderings of an atom, the work a lookup is not to repeat."""
    calls = []
    original = Node.to_unicode_str

    def counting(self):
        if isinstance(self, Atom):
            calls.append(self)
        return original(self)

    monkeypatch.setattr(Node, "to_unicode_str", counting)
    return calls


ALICE_LIKES = Atom("Likes", [Constant("alice"), Constant("bob")])


@pytest.mark.parametrize("table", [
    {"Likes(alice, bob)"}, {"Likes(alice, bob)": 1.0}, set(), {}, {"P": 1.0}])
def test_an_atom_whose_spellings_are_one_string_is_rendered_once_per_lookup(renderings, table):
    find_key(table, ALICE_LIKES)
    assert len(renderings) == 1


def test_an_atom_with_a_quoted_constant_found_in_a_set_by_its_key_is_rendered_once(renderings):
    # a set cannot hold two values for the atom, so the second spelling is not looked for
    assert find_key({LIKES_KEY}, LIKES) == LIKES_KEY
    assert len(renderings) == 1


def test_an_atom_with_a_quoted_constant_in_a_mapping_is_rendered_twice(renderings):
    # the key, and the text, which is checked for a second entry with another value
    assert find_key({LIKES_KEY: 1.0}, LIKES) == LIKES_KEY
    assert len(renderings) == 2


def test_an_atom_with_a_quoted_constant_in_no_spelling_is_rendered_twice(renderings):
    assert find_key({"P": 1.0}, LIKES) is None
    assert len(renderings) == 2


def test_the_kripke_evaluator_renders_an_atom_of_bare_constants_once(renderings):
    model = KripkeModel({0}, valuation={0: {"Likes(alice, bob)"}})
    assert satisfies_modal(ALICE_LIKES, model, 0) is True
    assert len(renderings) == 1


# ---------------------------------------------------------------------------
# A key that holds a complete quoted constant is the other spelling of another atom's key
# ---------------------------------------------------------------------------
#
# A key writes every name as it is, so a quote in a key is part of a name. The text of a formula
# writes a quote only around a constant. Each key below is, read as the text of a formula, another
# atom than the one it was made for:
#
#   name(s) of the atom                 key              the atom that TEXT is
#   Constant("'a'")                     P('a')           P over the constant a
#   Constant("ab, 'b'")                 P(ab, 'b')       P over the constants ab and b
#   Constant("f('b')")                  P(f('b'))        P over the term f(b)
#   Constant("'a"), Constant("b'")      P('a, b')        P over the constant named "a, b"
#   the proposition named P('a')        P('a')           P over the constant a
#   Variable("'x'")                     P('x')           P over the constant x

QUOTED_NAMES = ["'a'", "'k2'", "'a b'", "'a\\'b'", "'it\\\\s'"]


@pytest.mark.parametrize("name", QUOTED_NAMES)
def test_a_name_that_is_a_complete_quoted_constant_is_refused_where_a_key_is_made(name):
    atom = Atom("P", [Constant(name)])
    with pytest.raises(NotImplementedError) as info:
        atom_key(atom)
    message = str(info.value)
    assert "reads as the text of another atom" in message
    assert repr("P(" + name + ")") in message
    with pytest.raises(NotImplementedError):
        AtomKeys("the route").key(atom)
    with pytest.raises(NotImplementedError):
        other_key(atom)


def test_the_refusal_names_the_constant_the_key_would_be_taken_for():
    with pytest.raises(NotImplementedError) as info:
        atom_key(Atom("P", [Constant("'a'")]))
    assert str(info.value) == (
        "atom_key: the key of this atom, \"P('a')\", reads as the text of another atom. A key "
        "writes every name as it is, and a name here holds apostrophes, so the key holds 'a', "
        "which is how a formula writes the constant named \"a\" (in quotes). A valuation may be "
        "keyed by the key of an atom or by its text as a formula, so one entry would answer for "
        "two atoms. Rename the symbol (a name that merely holds an apostrophe, such as "
        "D'Alembert, is fine).")


@pytest.mark.parametrize("atom, key, quoted, other", [
    # one name that holds a quoted constant among other text
    (Atom("P", [Constant("ab, 'b'")]), "P(ab, 'b')", "'b'",
     Atom("P", [Constant("ab"), Constant("b")])),
    (Atom("P", [Constant("f('b')")]), "P(f('b'))", "'b'",
     Atom("P", [Function("f", [Constant("b")])])),
    # two names, one quote each, that make one quoted constant between them
    (Atom("P", [Constant("'a"), Constant("b'")]), "P('a, b')", "'a, b'",
     Atom("P", [Constant("a, b")])),
    # the quote is in the name of a proposition (a TPTP file writes one as 'P(\'a\')')
    (Atom("P('a')", []), "P('a')", "'a'", Atom("P", [Constant("a")])),
    # ... of a variable, of a function
    (Atom("P", [Variable("'x'")]), "P('x')", "'x'", Atom("P", [Constant("x")])),
    (Atom("P", [Function("f('b'), g", [Constant("cc")])]), "P(f('b'), g(cc))", "'b'",
     Atom("P", [Function("f", [Constant("b")]), Function("g", [Constant("cc")])])),
])
def test_a_key_that_is_the_text_of_another_atom_is_refused(atom, key, quoted, other):
    # the key the atom would get is, letter for letter, the text of ANOTHER atom as a formula
    assert key_text(atom) == key
    assert other.to_unicode_str() == key
    assert atom != other
    with pytest.raises(NotImplementedError) as info:
        atom_key(atom)
    message = str(info.value)
    assert repr(key) in message
    assert f"the key holds {quoted}, " in message
    # the other atom keeps its key, which holds no quote, and is found under either spelling
    assert "'" not in atom_key(other)
    assert find_key({key}, other) == key
    assert find_key({atom_key(other)}, other) == atom_key(other)


def test_one_entry_does_not_answer_for_two_atoms():
    # the valuation holds ONE string. It is the text of P over the constants ab and b ...
    two_constants = Atom("P", [Constant("ab"), Constant("b")])
    assert two_constants.to_unicode_str() == "P(ab, 'b')"
    model = KripkeModel({0}, valuation={0: {"P(ab, 'b')"}})
    assert satisfies_modal(two_constants, model, 0) is True
    # ... and would be the key of P over the one constant named  ab, 'b'  as well. That atom is
    # refused, so the entry cannot be read as a statement about it.
    one_constant = Atom("P", [Constant("ab, 'b'")])
    with pytest.raises(NotImplementedError, match="reads as the text of another atom"):
        satisfies_modal(one_constant, model, 0)


def test_control_without_the_refusal_one_entry_answers_for_two_atoms(monkeypatch):
    monkeypatch.setattr(atom_keys_module, "_refuse_key_that_reads_as_text",
                        lambda key, route, error: None)
    model = KripkeModel({0}, valuation={0: {"P(ab, 'b')"}})
    # two different atoms, one entry, both true: what the refusal is for
    assert satisfies_modal(Atom("P", [Constant("ab"), Constant("b")]), model, 0) is True
    assert satisfies_modal(Atom("P", [Constant("ab, 'b'")]), model, 0) is True


def test_the_refusal_of_a_quoted_name_uses_the_class_of_the_route():
    keys = AtomKeys("the route", "read", ValueError)
    with pytest.raises(ValueError) as info:
        keys.key(Atom("P", [Constant("'a'")]))
    assert str(info.value).startswith("the route: the key of this atom, \"P('a')\", reads as")
    with pytest.raises(ValueError):
        keys.find({"P('a')": 1}, Atom("P", [Constant("'a'")]))


def test_the_refusal_is_made_inside_an_evaluator_too():
    with pytest.raises(NotImplementedError):
        satisfies_modal(P(Constant("'a'")), KripkeModel({0}, valuation={0: {"P('a')"}}), 0)
    with pytest.raises(NotImplementedError):
        fuzzy_evaluate(P(Constant("'a'")), {"P('a')": 1.0})
    with pytest.raises(NotImplementedError):
        ltl_trace_satisfies(P(Constant("'a'")),
                            LTLTrace(prefix=(), cycle=(frozenset({"P('a')"}),)))


def test_the_check_is_on_the_safe_side():
    # P(rock 'n' roll) is the text of no formula (three words side by side are no term), yet the
    # key holds a quoted constant that stands free, and the check does not parse: it refuses
    with pytest.raises(NotImplementedError, match="the key holds 'n', "):
        atom_key(Atom("P", [Constant("rock 'n' roll")]))


@pytest.mark.parametrize("names, key", [
    (["D'Alembert"], "P(D'Alembert)"),
    (["3'-phosphate"], "P(3'-phosphate)"),
    (["'tis"], "P('tis)"),             # starts with a quote, ends with a letter
    (["a'"], "P(a')"),
    (["''"], "P('')"),                 # two quotes are no quoted constant (no empty name)
    (["''a''"], "P(''a'')"),           # an apostrophe next to each quote of 'a'
    # apostrophes next to digits: no quote of the name stands free at its opening side
    (["3',5'-cyclic AMP"], "P(3',5'-cyclic AMP)"),
    # two names with an apostrophe each: what lies between the two is  'Alembert, O'  with a
    # letter on either side
    (["D'Alembert", "O'Brien"], "P(D'Alembert, O'Brien)"),
    # 't Hooft, '  opens after "(" but closes in front of the letter t
    (["'t Hooft", "'t Hooft"], "P('t Hooft, 't Hooft)"),
])
def test_a_name_that_merely_holds_an_apostrophe_keeps_its_key(names, key):
    atom = Atom("P", [Constant(name) for name in names])
    assert atom_key(atom) == key
    assert AtomKeys("route").key(atom) == key
    # and the evaluators find the valuation typed that way
    assert satisfies_modal(atom, KripkeModel({0}, valuation={0: {key}}), 0) is True


def test_a_name_with_an_apostrophe_is_found_in_the_other_spelling_too():
    atom = Atom("P", [Constant("D'Alembert")])
    # the text of the formula escapes the apostrophe inside the quotes
    assert atom.to_unicode_str() == "P('D\\'Alembert')"
    model = KripkeModel({0}, valuation={0: {atom.to_unicode_str()}})
    assert satisfies_modal(atom, model, 0) is True
