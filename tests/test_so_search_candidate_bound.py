"""The bounded second-order searches answer for every domain size, or they raise.

``so_find_model``, ``so_find_countermodel``, ``so_is_satisfiable_finite`` and
``so_is_valid_finite`` look at the domain sizes ``1 .. max_size``. A size whose number of
candidate interpretations of the FREE symbols is above ``max_candidates`` is not searched, and a
search that left it out and said "valid" (or "no model") would be answering about structures it
never saw. So such a search raises ``CandidateBoundExceeded`` on reaching the size, unless it has
already found a structure at a smaller one: that structure is a witness whatever the larger sizes
hold.

The same four functions read a many-sorted formula by the one-universe reading (a sort is a
non-empty subset of the one domain, ``c:S`` is an element of ``S``, a sort and the unary predicate
of its name are one symbol), and read a predicate name as a free symbol of the structure wherever
no second-order quantifier of that name encloses it.

Every expectation below is derived by hand. Where only constants and predicates occur, the number
of candidates of a size ``k`` is

    (number of ways to partition the constants into at most k blocks) * 2 ** (k ** arity)

for each predicate: a constant assignment is counted up to renaming the domain elements.
"""

import pickle
import random

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.fol._so_nodes import SecondOrderQuantifier
from unicode_logic_kit.fol._truth_constants import TRUE
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Iff, Implies, Not, Or, Quantifier, SortedConstant, SortedQuantifier,
    Variable,
)
from unicode_logic_kit.semantics import modelfinder
from unicode_logic_kit.semantics import secondorder as so
from unicode_logic_kit.semantics.secondorder import (
    holds, so_find_countermodel, so_find_model, so_is_satisfiable_finite, so_is_valid_finite,
)
from unicode_logic_kit.semantics.tarski import check_structure

x, y = Variable("x"), Variable("y")
aa, bb, cc = Constant("aa"), Constant("bb"), Constant("cc")


def eq(left, right):
    return Atom("=", [left, right])


def R(left, right):
    return Atom("R", [left, right])


def P(term):
    return Atom("P", [term])


def forall(var, body):
    return Quantifier("∀", var, body)


def exists(var, body):
    return Quantifier("∃", var, body)


def sorted_forall(var, sort, body):
    return SortedQuantifier("∀", var, sort, body)


def sorted_exists(var, sort, body):
    return SortedQuantifier("∃", var, sort, body)


def refused(search, formula, **options):
    """The error a search must end in because it reached a size it does not enumerate."""
    with pytest.raises(ValueError) as raised:
        search(formula, **options)
    error = raised.value
    assert isinstance(error, so.CandidateBoundExceeded)
    return error


# R/2 is the only free symbol of the next three formulas: 2 ** (1 ** 2) = 2 interpretations on a
# 1-element domain, 2 ** (2 ** 2) = 16 on a 2-element one.

# "at most one element, or R is empty". One element satisfies the first disjunct. On two elements
# the first disjunct is false, and the formula fails exactly when R holds of some pair.
AT_MOST_ONE_OR_EMPTY = Or(forall(x, forall(y, eq(x, y))), forall(x, forall(y, Not(R(x, y)))))

# "two distinct elements, and R holds of some pair": no model on one element; on two elements any
# non-empty R is a model.
TWO_ELEMENTS_AND_R = And(exists(x, exists(y, Not(eq(x, y)))), exists(x, exists(y, R(x, y))))

# R(x, y) somewhere implies R holds of two DISTINCT elements somewhere: false on one element with
# R = {(0, 0)} (the antecedent holds, the consequent needs two elements).
R_IMPLIES_R_ON_DISTINCT = Implies(
    exists(x, exists(y, R(x, y))),
    exists(x, exists(y, And(Not(eq(x, y)), R(x, y)))))


# ---------------------------------------------------------------------------------------------
# a size over the bound is not searched, and not answered for
# ---------------------------------------------------------------------------------------------

def test_validity_is_not_answered_for_a_size_that_was_not_searched():
    # Size 1 has 2 candidates and is searched (no countermodel there). Size 2 has 16 > 15.
    error = refused(so_is_valid_finite, AT_MOST_ONE_OR_EMPTY, max_size=2, max_candidates=15)
    assert (error.size, error.candidates, error.max_candidates) == (2, 16, 15)
    message = str(error)
    assert "so_is_valid_finite" in message
    assert "domain size 2" in message
    assert "16" in message and "15" in message
    assert "R/2" in message
    assert "raise max_candidates to at least 16" in message
    assert "lower max_size to 1" in message


def test_with_room_for_the_size_the_countermodel_is_found():
    # 16 candidates fit in max_candidates = 16: a 2-element domain with R non-empty refutes it.
    assert so_is_valid_finite(AT_MOST_ONE_OR_EMPTY, max_size=2, max_candidates=16) is False
    counter = so_find_countermodel(AT_MOST_ONE_OR_EMPTY, max_size=2, max_candidates=16)
    assert counter is not None
    assert len(counter.domain) == 2
    assert counter.predicates[("R", 2)]          # R holds of some pair (the second disjunct fails)


def test_asking_only_about_the_sizes_that_fit_is_the_other_way_out():
    # max_size = 1 searches size 1 only (2 candidates): no countermodel there.
    assert so_is_valid_finite(AT_MOST_ONE_OR_EMPTY, max_size=1, max_candidates=15) is True


def test_a_countermodel_search_raises_like_the_validity_check():
    error = refused(so_find_countermodel, AT_MOST_ONE_OR_EMPTY, max_size=2, max_candidates=15)
    assert "so_find_countermodel" in str(error)
    assert error.size == 2


def test_satisfiability_is_not_denied_for_a_size_that_was_not_searched():
    # No model on one element (two distinct elements are needed); 16 > 15 candidates on two.
    error = refused(so_is_satisfiable_finite, TWO_ELEMENTS_AND_R, max_size=2, max_candidates=15)
    assert (error.size, error.candidates) == (2, 16)
    assert "so_is_satisfiable_finite" in str(error)
    assert "so_find_model" in str(
        refused(so_find_model, TWO_ELEMENTS_AND_R, max_size=2, max_candidates=15))


def test_with_room_for_the_size_the_model_is_found():
    assert so_is_satisfiable_finite(TWO_ELEMENTS_AND_R, max_size=2, max_candidates=16) is True
    model = so_find_model(TWO_ELEMENTS_AND_R, max_size=2, max_candidates=16)
    assert model is not None and len(model.domain) == 2 and model.predicates[("R", 2)]


def test_no_model_on_the_sizes_that_fit_is_still_an_answer():
    assert so_is_satisfiable_finite(TWO_ELEMENTS_AND_R, max_size=1, max_candidates=15) is False
    assert so_find_model(TWO_ELEMENTS_AND_R, max_size=1, max_candidates=15) is None


def test_a_structure_found_at_a_smaller_size_is_returned_whatever_the_larger_sizes_hold():
    # R = {(0, 0)} on one element refutes it (2 candidates there). Sizes 2 (16) and 3 (512) are
    # over the bound but never reached: the witness at size 1 is genuine on its own.
    counter = so_find_countermodel(R_IMPLIES_R_ON_DISTINCT, max_size=3, max_candidates=15)
    assert counter is not None
    assert len(counter.domain) == 1
    assert set(counter.predicates[("R", 2)]) == {(0, 0)}
    assert so_is_valid_finite(R_IMPLIES_R_ON_DISTINCT, max_size=3, max_candidates=15) is False


def test_the_first_size_over_the_bound_is_named_when_it_is_size_one():
    error = refused(so_is_valid_finite, AT_MOST_ONE_OR_EMPTY, max_size=2, max_candidates=1)
    assert error.size == 1
    assert error.candidates == 2
    assert "no smaller size" in str(error)


def test_the_error_is_a_value_error_and_survives_pickling():
    error = refused(so_is_valid_finite, AT_MOST_ONE_OR_EMPTY, max_size=2, max_candidates=15)
    assert isinstance(error, ValueError)
    again = pickle.loads(pickle.dumps(error))
    assert isinstance(again, so.CandidateBoundExceeded)
    assert (again.size, again.candidates, again.max_candidates) == (2, 16, 15)
    assert str(again) == str(error)


def test_a_ternary_relation_on_three_elements_is_refused_at_the_default_bound():
    # "at most two elements, or T is empty": valid on one and two elements (two of x, y, z always
    # coincide), refuted on three with T non-empty. T/3 on a 3-element domain has 2 ** 27 relations,
    # above the default max_candidates (2 ** 22), so size 3 is not searched and the answer for
    # max_size = 3 is not "valid".
    parse = MSFLParser(second_order=True).parse
    formula = parse("∀x ∀y ∀z (x = y ∨ y = z ∨ x = z) ∨ ∀x ∀y ∀z ¬T(x, y, z)")
    assert so_is_valid_finite(formula, max_size=2) is True
    for search in (so_is_valid_finite, so_find_countermodel):
        error = refused(search, formula, max_size=3)
        assert (error.size, error.candidates) == (3, 2 ** 27)
        assert error.max_candidates == so.MAX_RELATIONS == 2 ** 22
        assert "T/3" in str(error)


# ---------------------------------------------------------------------------------------------
# the number of candidates is the number the search would visit
# ---------------------------------------------------------------------------------------------

# Three constants, no predicate. A constant assignment is counted up to renaming the elements, so
# the number of candidates on k elements is the number of partitions of the three constants into
# at most k blocks: S(3,1) = 1, S(3,2) = 3, S(3,3) = 1. That is 1, 1 + 3 = 4, 1 + 3 + 1 = 5 for
# k = 1, 2, 3 (and not 3 ** 3 = 27 on three elements).
PIGEONHOLE = Or(Or(eq(aa, bb), eq(bb, cc)), eq(aa, cc))


def test_the_count_is_the_number_of_assignments_up_to_renaming_not_the_raw_power():
    # Valid on one and two elements (two of three constants must coincide); the three-element
    # domain with three different constants refutes it. 5 candidates fit in max_candidates = 5.
    assert so_is_valid_finite(PIGEONHOLE, max_size=2, max_candidates=4) is True
    assert so_is_valid_finite(PIGEONHOLE, max_size=3, max_candidates=5) is False
    counter = so_find_countermodel(PIGEONHOLE, max_size=3, max_candidates=5)
    assert counter is not None
    assert len(counter.domain) == 3
    assert len(set(counter.constants.values())) == 3


def test_one_candidate_fewer_and_the_size_is_refused_by_name():
    error = refused(so_is_valid_finite, PIGEONHOLE, max_size=3, max_candidates=4)
    assert (error.size, error.candidates, error.max_candidates) == (3, 5, 4)


def test_second_order_quantified_predicates_are_not_candidates():
    # ∃P ∀x P(x) has no free symbol: one candidate on every size, whatever 2 ** (k ** 1)
    # relations the quantifier ranges over.
    total = SecondOrderQuantifier("∃", "P", 1, forall(x, P(x)))
    assert so_is_valid_finite(total, max_size=4, max_candidates=1) is True


# ---------------------------------------------------------------------------------------------
# a predicate name that is free in one place and bound in another
# ---------------------------------------------------------------------------------------------

def test_a_predicate_free_outside_its_quantifier_is_interpreted_by_the_structure():
    # ¬P(bb) ∧ ∃P P(aa): the second conjunct is valid (take the bound P to be {aa}), so the
    # formula is equivalent to ¬P(bb) about the structure's OWN P, which fails when P holds of bb:
    # P = {(0,)} on one element. It is not valid.
    exists_p = SecondOrderQuantifier("∃", "P", 1, P(aa))
    formula = And(Not(P(bb)), exists_p)
    assert so_is_valid_finite(formula, max_size=2) is False
    counter = so_find_countermodel(formula, max_size=2)
    assert counter is not None and len(counter.domain) == 1
    assert set(counter.predicates[("P", 1)]) == {(0,)}
    assert holds(formula, counter) is False
    # Satisfiable: P empty makes ¬P(bb) true, and the second conjunct holds in every structure.
    assert so_is_satisfiable_finite(formula, max_size=1) is True


def test_a_model_that_needs_the_free_predicate_is_found():
    # P(aa) with the structure's P, and ∃P ¬P(aa) with a bound one: P = {(0,)} on one element makes
    # the first conjunct true, and the bound P can still be taken empty.
    formula = And(P(aa), SecondOrderQuantifier("∃", "P", 1, Not(P(aa))))
    model = so_find_model(formula, max_size=1)
    assert model is not None
    assert set(model.predicates[("P", 1)]) == {(0,)}
    assert holds(formula, model) is True


def test_a_name_bound_in_every_occurrence_is_not_a_symbol_of_the_structure():
    only_bound = SecondOrderQuantifier("∀", "P", 1, Implies(P(aa), P(aa)))
    assert so_is_valid_finite(only_bound, max_size=2, max_candidates=1) is True
    nested = SecondOrderQuantifier("∃", "P", 1, And(P(aa), SecondOrderQuantifier("∃", "P", 1, P(bb))))
    # The free symbols are the constants aa, bb and nothing else: counted up to renaming, 1
    # assignment on one element and 2 on two (aa = bb, aa ≠ bb), and no predicate factor. So the
    # sentence is satisfiable on one element within a bound of 1, and its negation, which has no
    # model, reaches size 2 and is refused there with 2 candidates.
    assert so_is_satisfiable_finite(nested, max_size=1, max_candidates=1) is True
    error = refused(so_is_satisfiable_finite, Not(nested), max_size=2, max_candidates=1)
    assert (error.size, error.candidates) == (2, 2)


def _free_names(node, bound=frozenset()):
    """The predicate names of ``node``'s atoms that no enclosing quantifier of that name binds."""
    if isinstance(node, SecondOrderQuantifier):
        return _free_names(node.formula, bound | {node.predicate})
    found = {node.predicate} if isinstance(node, Atom) and node.predicate not in bound else set()
    for child in node._child_nodes():
        found |= _free_names(child, bound)
    return found


def _random_second_order(rng, depth, bound_vars):
    names = ["P", "Q"]
    if depth == 0 or rng.random() < 0.15:
        term = rng.choice(bound_vars) if bound_vars and rng.random() < 0.6 else rng.choice([aa, bb])
        return Atom(rng.choice(names), [term])
    kind = rng.random()
    if kind < 0.15:
        return Not(_random_second_order(rng, depth - 1, bound_vars))
    if kind < 0.45:
        connective = rng.choice([And, Or, Implies])
        return connective(_random_second_order(rng, depth - 1, bound_vars),
                          _random_second_order(rng, depth - 1, bound_vars))
    if kind < 0.7:
        var = rng.choice([x, y])
        return Quantifier(rng.choice(["∀", "∃"]), var,
                          _random_second_order(rng, depth - 1, bound_vars + [var]))
    return SecondOrderQuantifier(rng.choice(["∀", "∃"]), rng.choice(names), 1,
                                 _random_second_order(rng, depth - 1, bound_vars))


def _renamed_apart(node, env, counter):
    """``node`` with every bound predicate variable given a name of its own (``env`` maps a name to
    the one it currently stands for)."""
    if isinstance(node, SecondOrderQuantifier):
        counter[0] += 1
        fresh = f"{node.predicate}_bound{counter[0]}"
        return SecondOrderQuantifier(
            node.type, fresh, node.arity,
            _renamed_apart(node.formula, {**env, node.predicate: fresh}, counter))
    if isinstance(node, Atom):
        return Atom(env.get(node.predicate, node.predicate), node.args)
    return node.map_children(lambda child: _renamed_apart(child, env, counter))


def test_a_name_that_is_free_and_bound_gives_the_verdicts_of_the_renamed_apart_formula():
    # Renaming every bound predicate variable to a name of its own does not change what a formula
    # says, and leaves no name that is both free and bound.
    rng = random.Random(20261005)
    mixed = 0
    for _ in range(200):
        formula = _random_second_order(rng, 3, [])
        apart = _renamed_apart(formula, {}, [0])
        bound = {n.predicate for n in formula.walk() if isinstance(n, SecondOrderQuantifier)}
        mixed += bool(_free_names(formula) & bound)
        text = formula.to_unicode_str()
        assert so_is_valid_finite(formula, max_size=2) == so_is_valid_finite(apart, max_size=2), text
        assert (so_is_satisfiable_finite(formula, max_size=2)
                == so_is_satisfiable_finite(apart, max_size=2)), text
    assert mixed >= 15       # the sample really has names that are free in one place, bound in another


# ---------------------------------------------------------------------------------------------
# many-sorted input: the one-universe reading
# ---------------------------------------------------------------------------------------------

@pytest.mark.parametrize("search", [so_find_model, so_find_countermodel,
                                    so_is_satisfiable_finite, so_is_valid_finite])
def test_a_many_sorted_formula_is_searched_by_every_function(search):
    parse = MSFLParser(second_order=True, many_sorted=True).parse
    search(parse("∃x:S ⊤"), max_size=2)          # answers; ends in no error


def test_a_sort_is_never_empty_so_an_existential_over_it_is_valid():
    parse = MSFLParser(second_order=True, many_sorted=True).parse
    assert so_is_valid_finite(parse("∃x:S ⊤"), max_size=2) is True
    assert so_find_countermodel(parse("∃x:S ⊤"), max_size=2) is None
    assert so_is_valid_finite(
        Implies(sorted_forall(x, "S", P(x)), exists(x, P(x))), max_size=3) is True


def test_a_sort_may_hold_two_elements_and_a_property_may_split_it():
    # ∃x:S P(x) → ∀x:S P(x): with one element in S the two coincide. On two elements S can be the
    # whole domain and P = {0} makes the antecedent true and the consequent false.
    formula = Implies(sorted_exists(x, "S", P(x)), sorted_forall(x, "S", P(x)))
    assert so_is_valid_finite(formula, max_size=1) is True
    counter = so_find_countermodel(formula, max_size=2)
    assert counter is not None
    universe = set(counter.sorts["S"])
    relation = counter.predicates[("P", 1)]
    assert len(universe) == 2
    assert any((d,) in relation for d in universe) and not all((d,) in relation for d in universe)
    check_structure(counter, formula)
    assert holds(formula, counter) is False


def test_second_order_quantifiers_range_over_the_whole_domain_not_over_a_sort():
    # ∃Q (∀x:S Q(x) ∧ ∃x ¬Q(x)) needs an element outside S: on one element S is the domain and
    # the two conjuncts clash on it; on two elements S = {0} and Q = {0} is a model.
    formula = SecondOrderQuantifier(
        "∃", "Q", 1, And(sorted_forall(x, "S", Atom("Q", [x])), exists(x, Not(Atom("Q", [x])))))
    assert so_find_model(formula, max_size=1) is None
    assert so_is_satisfiable_finite(formula, max_size=1) is False
    model = so_find_model(formula, max_size=2)
    assert model is not None
    assert len(model.domain) == 2 and len(model.sorts["S"]) == 1
    check_structure(model, formula)
    assert holds(formula, model) is True


def test_a_sorted_constant_lies_in_its_sort_and_a_plain_one_need_not():
    sorted_c = SortedConstant("cc", "S")
    member = Implies(sorted_forall(x, "S", P(x)), P(sorted_c))
    assert so_is_valid_finite(member, max_size=3) is True
    # The same with a constant that is NOT annotated: valid on one element (S is everything),
    # refuted on two (S = {0}, cc = 1, P = {0}).
    plain = Implies(sorted_forall(x, "S", P(x)), P(cc))
    assert so_is_valid_finite(plain, max_size=1) is True
    assert so_is_valid_finite(plain, max_size=2) is False
    counter = so_find_countermodel(plain, max_size=2)
    assert counter.constants["cc"] not in counter.sorts["S"]
    assert all((d,) in counter.predicates[("P", 1)] for d in counter.sorts["S"])


def test_a_constant_written_with_two_sorts_lies_in_both():
    # cc:S and cc:T are one constant, which lies in S and in T. The antecedent says P holds of all
    # of S and of none of T; cc would have to satisfy P and ¬P, so no structure satisfies the
    # antecedent and the implication is valid (its consequent, ¬(cc = cc), is false). Were cc
    # allowed outside one of the sorts, S and T disjoint with P = S would refute it.
    both = Implies(And(sorted_forall(x, "S", P(x)), sorted_forall(x, "T", Not(P(x)))),
                   Not(eq(SortedConstant("cc", "S"), SortedConstant("cc", "T"))))
    assert so_is_valid_finite(both, max_size=3) is True


def test_a_sort_and_the_unary_predicate_of_its_name_are_one_symbol():
    # S(x) for x in S holds: the predicate S IS the sort.
    assert so_is_valid_finite(sorted_forall(x, "S", Atom("S", [x])), max_size=3) is True
    # And the extension is the sort's: some element of a 2-element domain can lie outside S.
    outside = Not(forall(x, Atom("S", [x])))
    formula = And(sorted_exists(x, "S", TRUE), outside)
    model = so_find_model(formula, max_size=2)
    assert model is not None and len(model.sorts["S"]) == 1
    assert set(model.predicates[("S", 1)]) == {(d,) for d in model.sorts["S"]}


@pytest.mark.parametrize("search", [so_find_model, so_find_countermodel,
                                    so_is_satisfiable_finite, so_is_valid_finite])
def test_a_bound_predicate_named_like_a_sort_is_refused_by_name(search):
    # ∃S ∀x:S S(x): the quantifier would rebind the predicate half of the symbol S, not the sort.
    formula = SecondOrderQuantifier("∃", "S", 1, sorted_forall(x, "S", Atom("S", [x])))
    with pytest.raises(NotImplementedError, match="name of a sort"):
        search(formula, max_size=2)


def test_the_candidate_count_of_a_sorted_search_is_an_upper_bound_and_says_so():
    # Sort S: 2 ** 1 - 1 = 1 universe on one element, 2 ** 2 - 1 = 3 on two; P/1: 2 ** k.
    # On two elements that is 3 * 4 = 12 at most.
    formula = Implies(sorted_exists(x, "S", P(x)), sorted_forall(x, "S", P(x)))
    error = refused(so_is_valid_finite, formula, max_size=2, max_candidates=11)
    assert error.candidates == 12
    assert "at most 12" in str(error)
    assert "sort S" in str(error)


# ---------------------------------------------------------------------------------------------
# the search with the ASP check (fast=True) and a sort
# ---------------------------------------------------------------------------------------------

def test_the_asp_check_refuses_a_sort_inside_a_second_order_quantifier_by_name():
    pytest.importorskip("clingo")
    inside = SecondOrderQuantifier("∃", "Q", 1, sorted_forall(x, "S", Atom("Q", [x])))
    assert so_is_valid_finite(inside, max_size=2) is True          # Q = the whole domain
    with pytest.raises(ValueError, match="SortedQuantifier"):
        so_is_valid_finite(inside, max_size=2, fast=True)
    constant_inside = SecondOrderQuantifier("∃", "Q", 1, Atom("Q", [SortedConstant("cc", "S")]))
    with pytest.raises(ValueError, match="SortedConstant"):
        so_is_valid_finite(constant_inside, max_size=2, fast=True)


def test_the_asp_check_reads_a_sort_outside_every_second_order_quantifier_as_the_default_does():
    pytest.importorskip("clingo")
    outside = sorted_exists(x, "S", TRUE)
    assert so_is_valid_finite(outside, max_size=2, fast=True) is True
    model = so_find_model(outside, max_size=2, fast=True)
    assert model is not None and model.sorts["S"]


# ---------------------------------------------------------------------------------------------
# a random many-sorted first-order formula is decided as the model finder decides it
# ---------------------------------------------------------------------------------------------

SORTS = ["S", "T"]


def _random_sorted_term(rng, bound_vars):
    choice = rng.random()
    if choice < 0.55 and bound_vars:
        return rng.choice(bound_vars)
    if choice < 0.7:
        return SortedConstant("aa", "S")
    if choice < 0.8:
        return SortedConstant("cc", "T")
    return Constant("bb")


def _random_sorted_atom(rng, bound_vars):
    kind = rng.random()
    if kind < 0.45:
        return Atom("P", [_random_sorted_term(rng, bound_vars)])
    if kind < 0.75:
        return Atom("R", [_random_sorted_term(rng, bound_vars), _random_sorted_term(rng, bound_vars)])
    if kind < 0.9:
        return eq(_random_sorted_term(rng, bound_vars), _random_sorted_term(rng, bound_vars))
    return Atom(rng.choice(SORTS), [_random_sorted_term(rng, bound_vars)])   # a sort as a predicate


def _random_sorted_formula(rng, depth, bound_vars):
    if depth == 0:
        return _random_sorted_atom(rng, bound_vars)
    kind = rng.random()
    if kind < 0.15:
        return Not(_random_sorted_formula(rng, depth - 1, bound_vars))
    if kind < 0.45:
        connective = rng.choice([And, Or, Implies, Iff])
        return connective(_random_sorted_formula(rng, depth - 1, bound_vars),
                          _random_sorted_formula(rng, depth - 1, bound_vars))
    var = rng.choice([x, y])
    quantifier = rng.choice(["∀", "∃"])
    body = _random_sorted_formula(rng, depth - 1, bound_vars + [var])
    if rng.random() < 0.6:
        return SortedQuantifier(quantifier, var, rng.choice(SORTS), body)
    return Quantifier(quantifier, var, body)


def test_a_many_sorted_formula_without_a_second_order_quantifier_is_decided_like_the_model_finder():
    # With no second-order quantifier the search enumerates the structures of the model finder
    # (sizes 1 and 2) and evaluates them with its own evaluator: both must find a (counter)model
    # for the same formulas, and a structure it returns must be a structure of the definition in
    # which the formula has the value the search claims.
    rng = random.Random(20261006)
    countermodels = valid = models = 0
    for _ in range(120):
        formula = _random_sorted_formula(rng, rng.choice([2, 3]), [])
        text = formula.to_unicode_str()
        counter = so_find_countermodel(formula, max_size=2)
        reference = modelfinder.find_countermodel([], formula, max_size=2)
        assert (counter is None) == (reference is None), text
        if counter is not None:
            check_structure(counter, formula)
            assert holds(formula, counter) is False, text
            countermodels += 1
        else:
            valid += 1
        model = so_find_model(formula, max_size=2)
        assert (model is None) == (modelfinder.find_model([formula], max_size=2) is None), text
        if model is not None:
            check_structure(model, formula)
            assert holds(formula, model) is True, text
            models += 1
    assert countermodels >= 30 and valid >= 5 and models >= 30      # the sample is not one-sided
