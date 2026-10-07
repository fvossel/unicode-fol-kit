"""A valuation is keyed by the name of a constant, not by the way a formula writes it.

The text of a formula writes a constant in quotes where the bare name would read as
something else: the constant ``a`` is ``'a'`` there (``P('a')``), because ``a`` alone is a
variable. A valuation, a model table or a probabilistic program is keyed by the text of an
atom with every constant written by its NAME: the user types ``"P(a)"`` for the atom ``P`` of
the element ``a``, and an evaluator that grounds ``∀x P(x)`` over the domain ``{"a", "b"}``
substitutes ``Constant("a")`` and looks the atom up by that key. If the lookup used the text
of the formula (``P('a')``), a valuation typed the way it always was would be read as holding
neither atom, and a route that treats a missing key as false (the Kripke evaluator) would
answer a plain, wrong ``False``.

Every expected value below is worked out by hand from the definition of the semantics and
written as a literal. Each family of routes gets

* a universally quantified formula that is true only if BOTH keys are found, and one that is
  false because a key is absent or false,
* a control that shows the check can fail: the same call with the lookup replaced by the
  text of the formula gives the wrong answer,
* the formula read from text with a quoted constant, ``P('a')``, which meets the same key as
  the atom grounded from the element ``a`` (the constant ``a`` IS the element ``a``),
* and, where the route refused the pair before (a free variable ``x`` and a constant named
  ``x`` write one key), the pair written as text, ``P(x)`` next to ``P('x')``, which is still
  refused.

The models a route returns are keyed by the same names.
"""

from fractions import Fraction

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.fol import _atom_keys as atom_keys_module
from unicode_logic_kit.fol._msfl_nodes import key_text
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Implies, Not, Quantifier, Variable, Would,
)
from unicode_logic_kit.prob import (
    ProbConstraint, ProbFact, ProbProgram, entailment_bounds, query,
)
from unicode_logic_kit.prob import distribution as prob_distribution
from unicode_logic_kit.semantics import manyvalued as mv
from unicode_logic_kit.semantics import matrix as mx
from unicode_logic_kit.semantics.conditional import (
    CounterfactualModel, cf_countermodel, cf_satisfies, cf_valid,
)
from unicode_logic_kit.semantics.fuzzy import evaluate as fuzzy_evaluate
from unicode_logic_kit.semantics.fuzzy_kripke import FuzzyKripkeModel, satisfies_fuzzy_modal
from unicode_logic_kit.semantics.intuitionistic import (
    IntKripkeModel, int_countermodel, int_valid,
)
from unicode_logic_kit.semantics.kripke import (
    KripkeModel, satisfies_modal, sorted_constant_violations,
)
from unicode_logic_kit.semantics.relevant import RelevantModel, rel_countermodel, rel_satisfies
from unicode_logic_kit.semantics.truthtable import is_tautology, truth_table
from unicode_logic_kit.eval.datasets import proofwriter as pw
from unicode_logic_kit.eval.datasets._base import DatasetExample


def formula_text(node):
    """The text of a formula: what a lookup would use if it did not use the key."""
    return node.to_unicode_str()


def parse(text, **mode):
    return MSFLParser(**mode).parse(text)


def P(term):
    return Atom("P", [term])


def Q(term):
    return Atom("Q", [term])


a, b, bb = Constant("a"), Constant("b"), Constant("bb")

FORALL_P = parse("∀x P(x)")
EXISTS_P = parse("∃x P(x)")

#: the text of an atom of two constants that both need quotes, and the key typed for it
LIKES_AB_TEXT, LIKES_AB_KEY = "Likes('a', 'b')", "Likes(a, b)"


def refused_as_one_key(call):
    """The call ends in the refusal of two atoms that have one key; the message is returned.

    A route says it with the exception class its callers already handle; the sphere
    semantics has always refused an atom with a free variable on its own account.
    """
    with pytest.raises((NotImplementedError, TypeError, ValueError)) as info:
        call()
    message = str(info.value)
    assert "are both written" in message or "free variable" in message
    return message


# ---------------------------------------------------------------------------
# The two texts are different strings, which is what the rest of the file relies on
# ---------------------------------------------------------------------------

def test_the_text_of_a_formula_quotes_the_constants_that_the_key_writes_by_name():
    atom = Atom("Likes", [a, b])
    assert atom.to_unicode_str() == LIKES_AB_TEXT
    assert atom_keys_module.atom_key(atom) == LIKES_AB_KEY


# ---------------------------------------------------------------------------
# Kripke: satisfies_modal over a domain
# ---------------------------------------------------------------------------

def kripke(true_keys, domain=("a", "b")):
    return KripkeModel({0}, valuation={0: set(true_keys)}, domain=set(domain))


def test_kripke_a_universal_is_true_when_both_keys_are_found():
    # P(a), P(b) hold: both instances of ∀x P(x) hold
    assert satisfies_modal(FORALL_P, kripke({"P(a)", "P(b)"}), 0) is True


def test_kripke_a_universal_is_false_when_one_key_is_absent():
    # P(b) is missing from the valuation, which is read as false: the instance P(b) fails
    assert satisfies_modal(FORALL_P, kripke({"P(a)"}), 0) is False


def test_kripke_an_existential_needs_one_key():
    assert satisfies_modal(EXISTS_P, kripke({"P(b)"}), 0) is True
    assert satisfies_modal(EXISTS_P, kripke(set()), 0) is False


def test_kripke_two_constants_are_both_written_by_name_in_the_key():
    # ∀x Likes(x, a) over {a, b} has the instances Likes(a, a) and Likes(b, a)
    every_x_likes_aa = Quantifier("∀", Variable("x"), Atom("Likes", [Variable("x"), a]))
    both = kripke({"Likes(a, a)", "Likes(b, a)"})
    assert satisfies_modal(every_x_likes_aa, both, 0) is True
    one = kripke({"Likes(a, a)"})
    assert satisfies_modal(every_x_likes_aa, one, 0) is False


def test_kripke_the_key_of_the_instance_is_looked_up_in_every_world_it_is_evaluated_at():
    # □∀x P(x): at world 0 the only successor is 1, whose domain is {a, b}
    model = KripkeModel(
        {0, 1}, relations={"alethic": {(0, 1)}},
        valuation={1: {"P(a)", "P(b)"}}, domains={0: {"a", "b"}, 1: {"a", "b"}})
    formula = Box(FORALL_P)
    assert satisfies_modal(formula, model, 0) is True
    short = KripkeModel(
        {0, 1}, relations={"alethic": {(0, 1)}},
        valuation={1: {"P(a)"}}, domains={0: {"a", "b"}, 1: {"a", "b"}})
    assert satisfies_modal(formula, short, 0) is False


def test_kripke_a_sorted_quantifier_grounds_to_the_same_keys():
    # ∀x:Human Mortal(x) is ∀x (Human(x) → Mortal(x)); over {a, b}
    formula = parse("∀x:Human Mortal(x)", many_sorted=True)
    # only a is human, and a is mortal: b's instance is vacuously true
    assert satisfies_modal(formula, kripke({"Human(a)", "Mortal(a)"}), 0) is True
    # b is human as well and not mortal: its instance fails
    assert satisfies_modal(
        formula, kripke({"Human(a)", "Human(b)", "Mortal(a)"}), 0) is False


def test_kripke_the_guard_atom_of_a_sorted_constant_is_found_by_its_key():
    formula = parse("Mortal('a':Human)", many_sorted=True)
    held = kripke({"Human(a)"}, domain=())
    assert sorted_constant_violations(formula, held) == []
    missing = kripke(set(), domain=())
    assert sorted_constant_violations(formula, missing) == [("a", "Human", 0)]


def test_kripke_a_quoted_constant_read_from_text_meets_the_key_of_the_grounded_atom():
    formula = parse("P('a') ∧ ∀x P(x)")
    assert formula == And(P(a), FORALL_P)
    assert satisfies_modal(formula, kripke({"P(a)", "P(b)"}), 0) is True
    # P('b') alone, over the domain {b}: the constant b is the element b
    only_b = kripke({"P(b)"}, domain={"b"})
    assert satisfies_modal(parse("P('b')"), only_b, 0) is True
    assert satisfies_modal(parse("P('a')"), only_b, 0) is False


def test_kripke_control_a_lookup_by_the_text_of_the_formula_reads_the_model_as_false(monkeypatch):
    model = kripke({"P(a)", "P(b)"})
    assert satisfies_modal(FORALL_P, model, 0) is True
    monkeypatch.setattr(atom_keys_module, "key_text", formula_text)
    assert satisfies_modal(FORALL_P, model, 0) is False
    # and a model keyed by the text of the formula is the one that would then be found
    assert satisfies_modal(FORALL_P, kripke({"P('a')", "P('b')"}), 0) is True


def test_kripke_a_valuation_keyed_by_the_text_of_the_formula_is_read_as_the_atoms():
    # the quoted text is the other way to write the key of an atom: the guide taught it for a
    # hand-built atom, and a model typed that way means ``P`` of the elements ``a`` and ``b``
    assert satisfies_modal(FORALL_P, kripke({"P('a')", "P('b')"}), 0) is True
    # one instance short is still false
    assert satisfies_modal(FORALL_P, kripke({"P('a')"}), 0) is False


# ---------------------------------------------------------------------------
# The fuzzy evaluator
# ---------------------------------------------------------------------------

FUZZY_FORALL = parse("∀x P(x)", fuzzy=True)
FUZZY_EXISTS = parse("∃x P(x)", fuzzy=True)


def test_fuzzy_a_universal_is_the_least_degree_over_both_keys():
    assert fuzzy_evaluate(FUZZY_FORALL, {"P(a)": 1.0, "P(b)": 1.0}, domain={"a", "b"}) == 1.0
    # inf of 1.0 and 0.25
    assert fuzzy_evaluate(FUZZY_FORALL, {"P(a)": 1.0, "P(b)": 0.25}, domain={"a", "b"}) == 0.25


def test_fuzzy_an_existential_is_the_greatest_degree():
    assert fuzzy_evaluate(FUZZY_EXISTS, {"P(a)": 0.25, "P(b)": 0.75}, domain={"a", "b"}) == 0.75


def test_fuzzy_a_key_that_is_absent_is_named_by_the_name_of_the_constant():
    with pytest.raises(KeyError) as info:
        fuzzy_evaluate(FUZZY_FORALL, {"P(a)": 1.0}, domain={"a", "b"})
    message = str(info.value)
    assert "P(b)" in message and "P('b')" not in message


def test_fuzzy_a_sorted_universal_ranges_over_the_keys_of_its_universe():
    formula = parse("∀x:Person Tall(x)", many_sorted=True, fuzzy=True)
    degrees = {"Tall(a)": 1.0, "Tall(b)": 0.5}
    assert fuzzy_evaluate(formula, degrees, sort_universes={"Person": {"a", "b"}}) == 0.5


def test_fuzzy_a_quoted_constant_read_from_text_meets_the_key_of_the_grounded_atom():
    formula = parse("P('a')", fuzzy=True)
    assert formula == P(a)
    assert fuzzy_evaluate(formula, {"P(a)": 0.5}) == 0.5


def test_fuzzy_the_pair_of_a_free_variable_and_a_constant_of_one_name_is_refused():
    pair = parse("P(x) → P('x')", fuzzy=True)
    refused_as_one_key(lambda: fuzzy_evaluate(pair, {"P(x)": 1.0}))


def test_fuzzy_control_a_lookup_by_the_text_of_the_formula_misses_the_keys(monkeypatch):
    valuation = {"P(a)": 1.0, "P(b)": 1.0}
    assert fuzzy_evaluate(FUZZY_FORALL, valuation, domain={"a", "b"}) == 1.0
    monkeypatch.setattr(atom_keys_module, "key_text", formula_text)
    with pytest.raises(KeyError):
        fuzzy_evaluate(FUZZY_FORALL, valuation, domain={"a", "b"})


# ---------------------------------------------------------------------------
# The three-valued evaluator and its deciders
# ---------------------------------------------------------------------------

def test_manyvalued_a_universal_is_the_least_value_over_both_keys():
    valuation = {"P(a)": 1.0, "P(b)": 0.5}
    assert mv.kleene_value(FORALL_P, valuation, domain={"a", "b"}) == 0.5
    assert mv.kleene_value(EXISTS_P, valuation, domain={"a", "b"}) == 1.0


def test_manyvalued_a_key_that_is_absent_is_refused_by_the_name_of_the_constant():
    with pytest.raises(KeyError) as info:
        mv.kleene_value(FORALL_P, {"P(a)": 1.0}, domain={"a", "b"})
    assert "P(b)" in str(info.value) and "P('b')" not in str(info.value)


def test_manyvalued_the_premises_and_the_grounded_universal_share_their_letters():
    # K3: P(a), P(b) ⊨ ∀x P(x) over {a, b}; P(a) alone does not (P(b) = 0 falsifies the conclusion)
    assert mv.entails([P(a), P(b)], FORALL_P, "K3", domain={"a", "b"}) is True
    assert mv.entails([P(a)], FORALL_P, "K3", domain={"a", "b"}) is False


def test_manyvalued_a_quoted_constant_read_from_text_meets_the_key_of_the_grounded_atom():
    # (P(a) ∧ P(b)) → P(a) is LP-valid: with value m = min(P(a), P(b)) the implication is
    # max(1 - m, P(a)) >= 1/2 whatever the two values are. As two separate letters it would not be.
    formula = parse("∀x P(x) → P('a')")
    assert mv.is_valid(formula, "LP", domain={"a", "b"}) is True
    assert mv.is_valid(parse("∀x P(x) → P('a')"), "K3", domain={"a", "b"}) is False


def test_manyvalued_the_pair_of_a_free_variable_and_a_constant_of_one_name_is_refused():
    pair = parse("P(x) → P('x')")
    refused_as_one_key(lambda: mv.is_valid(pair, "LP"))
    refused_as_one_key(lambda: mv.kleene_value(pair, {"P(x)": 1.0}))


def test_manyvalued_control_a_lookup_by_the_text_of_the_formula_misses_the_keys(monkeypatch):
    valuation = {"P(a)": 1.0, "P(b)": 0.5}
    assert mv.kleene_value(FORALL_P, valuation, domain={"a", "b"}) == 0.5
    monkeypatch.setattr(atom_keys_module, "key_text", formula_text)
    with pytest.raises(KeyError):
        mv.kleene_value(FORALL_P, valuation, domain={"a", "b"})


# ---------------------------------------------------------------------------
# The matrix evaluator
# ---------------------------------------------------------------------------

def test_matrix_a_universal_folds_the_conjunction_over_both_keys():
    # K3: conj is the minimum, disj the maximum
    valuation = {"P(a)": 1.0, "P(b)": 0.5}
    assert mx.matrix_value(FORALL_P, valuation, mx.K3_MATRIX, domain=["a", "b"]) == 0.5
    assert mx.matrix_value(EXISTS_P, valuation, mx.K3_MATRIX, domain=["a", "b"]) == 1.0


def test_matrix_a_four_valued_universal_folds_by_the_bits_of_the_values():
    # FDE: T = (1, 0), B = (1, 1); conj(T, B) = (1&1, 0|1) = (1, 1) = B; disj(T, B) = (1|1, 0&1) = T
    valuation = {"P(a)": "T", "P(b)": "B"}
    assert mx.matrix_value(FORALL_P, valuation, mx.FDE_MATRIX, domain=["a", "b"]) == "B"
    assert mx.matrix_value(EXISTS_P, valuation, mx.FDE_MATRIX, domain=["a", "b"]) == "T"


def test_matrix_a_key_that_is_absent_is_refused_by_the_name_of_the_constant():
    with pytest.raises(KeyError) as info:
        mx.matrix_value(FORALL_P, {"P(a)": 1.0}, mx.K3_MATRIX, domain=["a", "b"])
    assert "P(b)" in str(info.value) and "P('b')" not in str(info.value)


def test_matrix_the_premises_and_the_grounded_universal_share_their_letters():
    assert mx.matrix_entails([P(a), P(b)], FORALL_P, mx.K3_MATRIX, domain=["a", "b"]) is True
    assert mx.matrix_entails([P(a)], FORALL_P, mx.K3_MATRIX, domain=["a", "b"]) is False


def test_matrix_a_quoted_constant_read_from_text_meets_the_key_of_the_grounded_atom():
    formula = parse("∀x P(x) → P('a')")
    assert mx.matrix_is_valid(formula, mx.LP_MATRIX, domain=["a", "b"]) is True
    assert mx.matrix_is_valid(formula, mx.K3_MATRIX, domain=["a", "b"]) is False


def test_matrix_the_pair_of_a_free_variable_and_a_constant_of_one_name_is_refused():
    pair = parse("P(x) → P('x')")
    refused_as_one_key(lambda: mx.matrix_is_valid(pair, mx.LP_MATRIX))
    refused_as_one_key(lambda: mx.matrix_value(pair, {"P(x)": 1.0}, mx.K3_MATRIX))


def test_matrix_control_a_lookup_by_the_text_of_the_formula_misses_the_keys(monkeypatch):
    valuation = {"P(a)": 1.0, "P(b)": 0.5}
    monkeypatch.setattr(atom_keys_module, "key_text", formula_text)
    with pytest.raises(KeyError):
        mx.matrix_value(FORALL_P, valuation, mx.K3_MATRIX, domain=["a", "b"])


# ---------------------------------------------------------------------------
# The truth table
# ---------------------------------------------------------------------------

def test_truth_table_the_columns_are_keys_and_the_last_header_is_the_text_of_the_formula():
    table = truth_table(Implies(P(a), Q(bb)))
    assert table.atoms == ("P(a)", "Q(bb)")
    # a is written in quotes in the formula (one letter reads as a variable), bb is not
    assert table.render().splitlines()[0] == "| P(a) | Q(bb) | P('a') → Q(bb) |"


def test_truth_table_a_quoted_constant_read_from_text_is_the_column_of_the_atom():
    assert truth_table(parse("P('a') → P(bb)")).atoms == ("P(a)", "P(bb)")


def test_truth_table_the_pair_of_a_free_variable_and_a_constant_of_one_name_is_refused():
    pair = parse("P(x) → P('x')")
    refused_as_one_key(lambda: truth_table(pair))
    refused_as_one_key(lambda: is_tautology(pair))


# ---------------------------------------------------------------------------
# The intuitionistic Kripke evaluator and search
# ---------------------------------------------------------------------------

def int_model(true_at, domains):
    # the chain 0 <= 1
    return IntKripkeModel({0: frozenset({0, 1}), 1: frozenset({1})}, true_at, domains)


def test_intuitionistic_a_universal_is_forced_when_every_key_is_found():
    # ∀x P(x) at 0 asks P(d) at every world w' >= 0 and every d in D(w'):
    # (0, a), (1, a), (1, b); P(a) holds at 0 and 1, P(b) at 1
    model = int_model({"P(a)": frozenset({0, 1}), "P(b)": frozenset({1})},
                      {0: frozenset({"a"}), 1: frozenset({"a", "b"})})
    assert model.forces(0, FORALL_P) is True


def test_intuitionistic_a_universal_is_not_forced_when_a_key_is_absent():
    model = int_model({"P(a)": frozenset({0, 1})},
                      {0: frozenset({"a"}), 1: frozenset({"a", "b"})})
    # P(b) is forced nowhere, and b exists at world 1
    assert model.forces(0, FORALL_P) is False


def test_intuitionistic_an_existential_needs_one_key_at_the_world():
    model = int_model({"P(a)": frozenset({0, 1})},
                      {0: frozenset({"a"}), 1: frozenset({"a", "b"})})
    assert model.forces(0, EXISTS_P) is True
    assert int_model({}, {0: frozenset({"a"}), 1: frozenset({"a"})}).forces(0, EXISTS_P) is False


def test_intuitionistic_a_quoted_constant_read_from_text_meets_the_key_of_the_grounded_atom():
    formula = parse("P('a') ∧ ∀x P(x)")
    model = int_model({"P(a)": frozenset({0, 1}), "P(b)": frozenset({1})},
                      {0: frozenset({"a"}), 1: frozenset({"a", "b"})})
    assert model.forces(0, formula) is True


@pytest.mark.parametrize("name, key", [
    ("a", "a"), ("k2", "k2"), ("Alice", "Alice"), ("G-910", "G-910"), ("_e0", "_e0"),
    ("1", "1"), ("a b", "a b"),
])
def test_intuitionistic_the_keys_of_a_returned_countermodel_hold_the_bare_name(name, key):
    constant = Constant(name)
    # P(c) → Q(c) is not valid: one world where P(c) is forced and Q(c) is not. The first model the
    # search reaches is the one-world order with P(c) true and Q(c) false.
    model, world = int_countermodel(Implies(P(constant), Q(constant)))
    assert world == 0
    assert model.valuation == {f"P({key})": frozenset({0}), f"Q({key})": frozenset()}


def test_intuitionistic_the_keys_of_a_first_order_countermodel_hold_the_bare_names():
    # P(a) → ∀x P(x): one world, the domain {a, _e0}; the first model the search reaches forces
    # P(a) and not P(_e0). The elements are sorted: "_e0" < "a".
    formula = Implies(P(a), Quantifier("∀", Variable("x"), P(Variable("x"))))
    model, world = int_countermodel(formula)
    assert world == 0
    assert model.domains == {0: frozenset({"a", "_e0"})}
    assert model.valuation == {"P(_e0)": frozenset(), "P(a)": frozenset({0})}
    assert int_valid(formula) is False


def test_intuitionistic_the_pair_of_a_free_variable_and_a_constant_of_one_name_is_refused():
    pair = parse("P(x) → P('x')")
    refused_as_one_key(lambda: int_valid(pair))
    refused_as_one_key(lambda: int_countermodel(pair))


def test_intuitionistic_control_a_lookup_by_the_text_of_the_formula_misses_the_keys(monkeypatch):
    model = int_model({"P(a)": frozenset({0, 1}), "P(b)": frozenset({1})},
                      {0: frozenset({"a"}), 1: frozenset({"a", "b"})})
    assert model.forces(0, FORALL_P) is True
    monkeypatch.setattr(atom_keys_module, "key_text", formula_text)
    assert model.forces(0, FORALL_P) is False


# ---------------------------------------------------------------------------
# The counterfactual (sphere) evaluator and search
# ---------------------------------------------------------------------------

def sphere_model(true_keys):
    return CounterfactualModel((0,), {0: frozenset(true_keys)}, {0: [frozenset({0})]})


def test_counterfactual_an_atom_of_a_constant_is_found_by_its_key():
    assert cf_satisfies(P(a), sphere_model({"P(a)"}), 0) is True
    assert cf_satisfies(P(a), sphere_model({"P(b)"}), 0) is False


def test_counterfactual_a_conditional_reads_its_atoms_by_key():
    # the one sphere {0} holds the antecedent world: the consequent must hold there
    conditional = Would(P(a), Q(a))
    assert cf_satisfies(conditional, sphere_model({"P(a)", "Q(a)"}), 0) is True
    assert cf_satisfies(conditional, sphere_model({"P(a)"}), 0) is False


def test_counterfactual_a_quoted_constant_read_from_text_meets_the_key():
    formula = parse("P('a') □→ Q('a')", modal=True)
    assert formula == Would(P(a), Q(a))
    assert cf_satisfies(formula, sphere_model({"P(a)", "Q(a)"}), 0) is True


@pytest.mark.parametrize("name", ["a", "k2", "Alice", "G-910", "_e0"])
def test_counterfactual_the_keys_of_a_returned_countermodel_hold_the_bare_name(name):
    constant = Constant(name)
    # one world, atoms P(c), Q(c) in key order: the valuations are tried as bits (P, Q) =
    # (F, F), (F, T), (T, F): the third makes P(c) → Q(c) false
    model, world = cf_countermodel(Implies(P(constant), Q(constant)), max_worlds=1)
    assert world == 0
    assert model.valuation == {0: frozenset({f"P({name})"})}


def test_counterfactual_the_pair_of_a_free_variable_and_a_constant_of_one_name_is_refused():
    pair = parse("P(x) → P('x')")
    refused_as_one_key(lambda: cf_valid(pair))
    refused_as_one_key(lambda: cf_countermodel(pair))


def test_counterfactual_control_a_lookup_by_the_text_of_the_formula_misses_the_key(monkeypatch):
    model = sphere_model({"P(a)"})
    assert cf_satisfies(P(a), model, 0) is True
    monkeypatch.setattr(atom_keys_module, "key_text", formula_text)
    assert cf_satisfies(P(a), model, 0) is False


# ---------------------------------------------------------------------------
# The relevant-logic evaluator: nullary atoms only
# ---------------------------------------------------------------------------

def test_relevant_a_nullary_atom_is_found_by_its_name():
    model = RelevantModel(("w0",), {"w0"}, valuation={"P": {"w0"}})
    assert rel_satisfies(model, "w0", Atom("P", [])) is True
    assert rel_satisfies(model, "w0", Atom("Q", [])) is False


def test_relevant_a_countermodel_is_keyed_by_the_names_of_the_atoms():
    # P → Q fails at the normal world in the one-world model where P holds and Q does not
    model, world = rel_countermodel(Implies(Atom("P", []), Atom("Q", [])), max_worlds=1)
    assert world == "w0"
    assert dict(model.valuation) == {"P": frozenset({"w0"}), "Q": frozenset()}


def test_relevant_an_atom_with_a_constant_is_refused_with_the_text_of_the_formula():
    # the route has no constants; the refusal shows the atom the way the formula writes it
    with pytest.raises(TypeError) as info:
        rel_satisfies(RelevantModel(("w0",), {"w0"}), "w0", P(a))
    assert "P('a')" in str(info.value)


def test_relevant_a_nullary_atom_has_one_text_for_the_key_and_for_the_formula():
    # the route reads no constant, so there is no key that could differ from the text of the formula
    nullary = Atom("P", [])
    assert key_text(nullary) == nullary.to_unicode_str() == "P"


# ---------------------------------------------------------------------------
# The graded Kripke evaluator
# ---------------------------------------------------------------------------

def test_fuzzy_kripke_an_atom_of_a_constant_is_read_at_the_degree_of_its_key():
    model = FuzzyKripkeModel({0, 1}, relations={"alethic": {(0, 1): 1.0}},
                             valuation={1: {"P(a)": 0.5}})
    # Box is the infimum of impl(R(0, w'), degree at w') over w' in {0, 1}:
    # w' = 0: R = 0, impl(0, 0.0) = min(1, 1 - 0 + 0) = 1; w' = 1: R = 1, impl(1, 0.5) = 0.5
    assert satisfies_fuzzy_modal(Box(P(a)), model, 0) == 0.5
    assert satisfies_fuzzy_modal(P(a), model, 1) == 0.5


def test_fuzzy_kripke_the_text_of_the_formula_is_read_as_the_key_of_an_atom():
    model = FuzzyKripkeModel({0}, valuation={0: {"P('a')": 0.5}})
    # a degree filed under the text of the formula is the degree of the atom, as one filed
    # under the key is
    assert satisfies_fuzzy_modal(P(a), model, 0) == 0.5
    # a degree filed under the text of the formula of ANOTHER atom is not
    assert satisfies_fuzzy_modal(P(b), model, 0) == 0.0


def test_fuzzy_kripke_control_a_lookup_by_the_text_of_the_formula_misses_the_key(monkeypatch):
    model = FuzzyKripkeModel({0}, valuation={0: {"P(a)": 0.5}})
    assert satisfies_fuzzy_modal(P(a), model, 0) == 0.5
    monkeypatch.setattr(atom_keys_module, "key_text", formula_text)
    assert satisfies_fuzzy_modal(P(a), model, 0) == 0.0


# ---------------------------------------------------------------------------
# The probabilistic routes
# ---------------------------------------------------------------------------

HALF = Fraction(1, 2)


def two_facts():
    return ProbProgram(facts=[ProbFact(P(a), HALF), ProbFact(P(b), HALF)], rules=[])


@pytest.mark.parametrize("method", ["enumerate", "compile"])
def test_prob_a_universal_goal_is_the_product_over_the_constants_of_the_program(method):
    # the constants are a and b: P(a) ∧ P(b) has probability 1/2 · 1/2
    assert query(two_facts(), FORALL_P, method=method) == Fraction(1, 4)
    # ∃x P(x): 1 − (1/2)(1/2)
    assert query(two_facts(), EXISTS_P, method=method) == Fraction(3, 4)


@pytest.mark.parametrize("method", ["enumerate", "compile"])
def test_prob_a_derived_atom_meets_the_key_of_the_fact_it_comes_from(method):
    # the rule ∀x (P(x) → Q(x)) grounds to P(a) → Q(a): Q(a) holds exactly when the fact P(a) does
    rule = Quantifier("∀", Variable("x"), Implies(P(Variable("x")), Q(Variable("x"))))
    program = ProbProgram(facts=[ProbFact(P(a), HALF)], rules=[rule])
    assert query(program, Q(a), method=method) == HALF
    # b is a constant of the goal: P(b) is no fact and no rule derives it
    assert query(program, Q(b), method=method) == Fraction(0)


def test_prob_a_hard_fact_and_a_rule_meet_in_one_key():
    rule = Quantifier("∀", Variable("x"), Implies(P(Variable("x")), Q(Variable("x"))))
    program = ProbProgram(facts=[], rules=[rule], hard_facts=[P(a)])
    assert query(program, Q(a)) == Fraction(1)


def test_prob_a_quoted_constant_read_from_text_meets_the_key_of_the_fact():
    assert query(two_facts(), parse("P('a')")) == HALF
    assert query(two_facts(), parse("P('a') ∧ P('b')")) == Fraction(1, 4)


def test_prob_bounds_a_quoted_constant_read_from_text_is_the_atom_of_the_constraint():
    constraints = [ProbConstraint.exact(P(a), Fraction(7, 10))]
    seven_tenths = (Fraction(7, 10), Fraction(7, 10))
    for strategy in ("direct", "column_generation"):
        same = entailment_bounds(constraints, parse("P('a')"), strategy=strategy)
        assert (same.lower, same.upper) == seven_tenths
        other = entailment_bounds(constraints, parse("P('b')"), strategy=strategy)
        assert (other.lower, other.upper) == (Fraction(0), Fraction(1))


def test_prob_bounds_the_pair_of_a_free_variable_and_a_constant_of_one_name_is_refused():
    constraints = [ProbConstraint.exact(parse("P(x)"), Fraction(7, 10))]
    for strategy in ("direct", "column_generation"):
        refused_as_one_key(lambda: entailment_bounds(constraints, parse("P('x')"), strategy=strategy))


def test_prob_control_a_derived_atom_is_lost_when_the_facts_are_keyed_by_the_text(monkeypatch):
    rule = Quantifier("∀", Variable("x"), Implies(P(Variable("x")), Q(Variable("x"))))
    fact = ProbFact(P(a), HALF)
    program = ProbProgram(facts=[fact], rules=[rule])
    assert query(program, Q(a)) == HALF
    # the fact keyed by the text of the formula (P('a')) and the rule body keyed by the name
    # (P(a)) are two different letters: the fact never reaches the rule, and Q(a) is never
    # derived (the grounded body atom is another object than the atom of the fact)
    real = prob_distribution.key_text
    monkeypatch.setattr(
        prob_distribution, "key_text",
        lambda node: formula_text(node) if node is fact.atom else real(node))
    assert query(program, Q(a)) == Fraction(0)


# ---------------------------------------------------------------------------
# The closed-world model of a ProofWriter theory
# ---------------------------------------------------------------------------

def test_proofwriter_the_closed_model_is_a_set_of_keys_with_the_names_of_the_constants():
    # P(a); ∀x (P(x) ∧ ¬R(x) → Q(x)): R(a) is not derivable, so Q(a) holds by negation as failure
    x = Variable("x")
    rule = Quantifier("∀", x, Implies(And(P(x), Not(Atom("R", [x]))), Q(x)))
    true_atoms, has_naf = pw._closed_model([P(a), rule], [a])
    assert true_atoms == frozenset({"P(a)", "Q(a)"})
    assert has_naf is True


def test_proofwriter_the_provenance_is_filed_under_signed_keys_with_the_names():
    x = Variable("x")
    rule = Quantifier("∀", x, Implies(And(P(x), Not(Atom("R", [x]))), Q(x)))
    negative_fact = Not(Atom("S", [a]))
    _, _, provenance = pw._closed_model([P(a), rule, negative_fact], [a], record_provenance=True)
    # premise 0 derives P(a); premise 1 derives Q(a) from P(a) and the absence of R(a);
    # premise 2 is the negative fact ¬S(a)
    assert provenance == {
        "P(a)": [(0, ())],
        "Q(a)": [(1, ("P(a)", "¬R(a)"))],
        "¬S(a)": [(2, ())],
    }


def test_proofwriter_a_closed_world_answer_records_the_key_of_each_atom_it_asked_about():
    example = DatasetExample(
        id="keys:1", nl_premises=(), fol_premises=("P('a')", "∀x (P(x) ∧ ¬R(x) → Q(x))"),
        nl_conclusion=None, fol_conclusion="Q('a')", label="True", known_bad=False, meta={})
    result = pw.solve_structured_example(example, semantics="cwa")
    assert result["predicted"] == "True"
    # a theory with a negated body is beyond the definite fragment: no prover is asked, and
    # the record holds the atom under its key
    assert result["atom_calls"] == [{"atom": "Q(a)", "derivable": True}]


def test_proofwriter_a_gold_proof_is_checked_against_the_signed_key_of_the_target():
    example = DatasetExample(
        id="keys:2", nl_premises=(), fol_premises=("¬P('b')",), nl_conclusion=None,
        fol_conclusion="¬P('b')", label="True", known_bad=False,
        meta={"premise_keys": ["triple1"], "proofs": "[(triple1)]", "strategy": "proof"})
    checked = pw.check_gold_proof(example)
    assert checked["kind"] == "derivation" and checked["ok"] is True
    assert checked["atom"] == "¬P(b)"


def test_proofwriter_control_a_closed_model_keyed_by_the_text_of_the_formula_loses_the_rule(monkeypatch):
    x = Variable("x")
    rule = Quantifier("∀", x, Implies(P(x), Q(x)))
    assert pw._closed_model([P(a), rule], [a])[0] == frozenset({"P(a)", "Q(a)"})
    monkeypatch.setattr(pw, "key_text", formula_text)
    # keyed by the text of the formula the model is still closed, but its keys are no longer the
    # names a user (and the gold proofs) write
    assert pw._closed_model([P(a), rule], [a])[0] == frozenset({"P('a')", "Q('a')"})
