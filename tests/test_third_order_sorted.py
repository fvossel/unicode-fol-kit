"""Third order over sorted individuals: the finite evaluator and the classical writers.

``MSFLParser(third_order=True, many_sorted=True)`` reads ``∀x:S`` and ``c:S`` next to
predicates in argument position. A sort restricts an INDIVIDUAL binder; a property and
a predicate quantifier range over the relations on the whole domain, with and without
sorts. So the typing of a slot is what it was, ``holds_to`` reads the sorted binder as
``satisfies_so`` does, and the writers state a sorted problem as the unsorted one plus
the two facts about its sorts.

The structure used below, with every extension written out:

    domain   0, 1, 2
    Human    {0, 1}                      a sort
    G        {0}                         a property
    H        {0, 1}                      the property with the extension of the sort
    Pos      {G, H}                      a predicate of properties
    alice = 0, bob = 1, rex = 2
"""

import itertools

import pytest

from unicode_logic_kit import (
    MSFLParser, holds, holds_to, satisfies_to, to_isabelle_to, to_thf_to,
)
from unicode_logic_kit.fol.nodes import Atom, Constant, Quantifier, Variable
from unicode_logic_kit.hol import to_isabelle_so, to_thf_so
from unicode_logic_kit.hol.isabelle_runner import check_theory, isabelle_available
from unicode_logic_kit.semantics import IllegalStructureError, Structure

_isa = pytest.mark.skipif(not isabelle_available(), reason="no local Isabelle installation")
_isa_live = pytest.mark.isabelle_live

TOS = MSFLParser(third_order=True, many_sorted=True).parse
TO = MSFLParser(third_order=True).parse
SOS = MSFLParser(second_order=True, many_sorted=True).parse

G = frozenset({(0,)})
H = frozenset({(0,), (1,)})
WORLD = Structure((0, 1, 2), sorts={"Human": {0, 1}},
                  predicates={("G", 1): {(0,)}, ("Pos", 1): {(G,), (H,)}},
                  constants={"alice": 0, "bob": 1, "rex": 2})


# ---------------------------------------------------------------------------
# The evaluator
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("text, expected", [
    ("Pos(G)", True),
    ("Pos(Human)", True),                        # the sort as a property: {0, 1} is H
    ("G(alice:Human)", True),
    ("G(bob:Human)", False),
    # 0 is in G and in H, 1 is in H: every human has a positive property.
    ("∀x:Human ∃P (Pos(P) ∧ P(x))", True),
    ("∀P (Pos(P) → ∃x:Human P(x))", True),
    ("∀P (Pos(P) → ∀x:Human P(x))", False),      # G does not hold of 1
    ("∃P (Pos(P) ∧ ∀x:Human P(x))", True),       # H
    ("∃P (Pos(P) ∧ ¬∃x:Human P(x))", False),     # both positive properties hold of 0
    # A predicate of properties that holds of G and not of its complement {1, 2}.
    ("∃Z (Z(G) ∧ ¬Z(λx. ¬G(x)))", True),
    # Comprehension over the humans: P = G if x is 0, the empty set otherwise.
    ("∀x:Human ∃P ∀y:Human (P(y) ↔ G(y) ∧ G(x))", True),
])
def test_holds_to_reads_a_sorted_binder_over_its_sort(text, expected):
    assert holds_to(TOS(text), WORLD) is expected


def test_the_unsorted_binder_ranges_over_everything_and_the_sorted_one_over_the_sort():
    """``∀x ∃P (Pos(P) ∧ P(x))`` fails at 2; the sorted one does not look at 2."""
    assert holds_to(TO("∀x ∃P (Pos(P) ∧ P(x))"), WORLD) is False
    assert holds_to(TOS("∀x:Human ∃P (Pos(P) ∧ P(x))"), WORLD) is True


def test_a_predicate_quantifier_is_not_restricted_to_a_sort():
    """Some property holds of no human and of the element 2: the set {2}. A quantifier
    over the subsets of the sort alone would find none."""
    world = Structure((0, 1, 2), sorts={"Human": {0, 1}, "Thing": {2}},
                      constants={"rex": 2})
    assert holds_to(TOS("∃P (¬∃x:Human P(x) ∧ P(rex:Thing))"), world) is True
    assert holds_to(TOS("∀P (P(rex:Thing) → ∃x:Human P(x))"), world) is False


def test_a_sorted_constant_outside_its_sort_is_an_illegal_structure():
    for text in ("G(rex:Human)", "Ess(G, rex:Human)", "∃P (P(rex:Human))"):
        with pytest.raises(IllegalStructureError, match="not in the sort"):
            holds_to(TOS(text), WORLD)


def test_an_empty_sort_is_an_illegal_structure():
    empty = Structure((0, 1), sorts={"Human": set()})
    with pytest.raises(IllegalStructureError):
        holds_to(TOS("∀x:Human ∃P P(x)"), empty)


def _structures():
    """Every structure on {0, 1} with a non-empty sort S and a unary Q."""
    domain = (0, 1)
    subsets = [set(c) for r in range(3) for c in itertools.combinations(domain, r)]
    for sort in subsets:
        if not sort:
            continue
        for q in subsets:
            yield Structure(domain, sorts={"S": sort},
                            predicates={("Q", 1): {(d,) for d in q}})


@pytest.mark.parametrize("text", [
    "∃P ∀x:S (P(x) ↔ Q(x))",
    "∀P (∀x:S P(x) → ∃x:S P(x))",
    "∃P (∃x:S P(x) ∧ ∃x:S ¬P(x))",          # true exactly when S has two elements
    "∀x:S ∃P (P(x) ∧ ∀y:S (P(y) → Q(y)))",   # true exactly when S is inside Q
    "∃x:S ∀P (P(x) → Q(x))",
])
def test_on_a_second_order_formula_holds_to_is_the_second_order_evaluator(text):
    """Without a property argument the two evaluators answer the same question, in
    every structure of the size."""
    third, second = TOS(text), SOS(text)
    assert third == second
    for structure in _structures():
        assert holds_to(third, structure) == holds(second, structure)


def test_the_two_hand_checked_rows_of_the_comparison():
    """Two of the formulas above have a plain condition; checked without either
    evaluator's help."""
    for structure in _structures():
        sort = structure.sort_universe("S")
        q = {t[0] for t in structure.predicates[("Q", 1)]}
        assert holds_to(TOS("∃P (∃x:S P(x) ∧ ∃x:S ¬P(x))"), structure) == (len(sort) == 2)
        assert holds_to(TOS("∀x:S ∃P (P(x) ∧ ∀y:S (P(y) → Q(y)))"), structure) == (
            set(sort) <= q)


# ---------------------------------------------------------------------------
# The writers
# ---------------------------------------------------------------------------

GOAL = "∃P (Pos(P) ∧ P(socrates:Human))"
ASSUMPTION = "∀x:Human ∃P (Pos(P) ∧ P(x))"


def test_isabelle_states_the_two_facts_about_the_sorts_before_the_assumptions():
    theory = to_isabelle_to(TOS(GOAL), assumptions=[TOS(ASSUMPTION)])
    assert 'consts Human :: "i \\<Rightarrow> bool"' in theory
    assert 'consts socrates :: "i"' in theory
    assert ('axiomatization where nonempty_sort0: "(\\<exists>x0::i. (Human x0))"'
            in theory)
    assert 'axiomatization where sort_member0: "(Human socrates)"' in theory
    assert ('axiomatization where assumption1: "(\\<forall>x::i. ((Human x) '
            '\\<longrightarrow> (\\<exists>P::i \\<Rightarrow> bool. ((Pos P) \\<and> (P x)))))"'
            in theory)
    assert ('lemma "(\\<exists>P::i \\<Rightarrow> bool. ((Pos P) \\<and> (P socrates)))"'
            in theory)
    assert theory.index("nonempty_sort0") < theory.index("sort_member0") < theory.index(
        "assumption1")


def test_thf_states_the_two_facts_about_the_sorts_before_the_assumptions():
    problem = to_thf_to(TOS(GOAL), assumptions=[TOS(ASSUMPTION)])
    assert "thf(human_type, type, ( human : $i > $o ))." in problem
    assert "thf(nonempty_sort0, axiom, ( ( ? [X0_V: $i] : ( human @ X0_V ) ) ))." in problem
    assert "thf(sort_member0, axiom, ( ( human @ socrates ) ))." in problem
    assert ("thf(assumption1, axiom, ( ( ! [X_V: $i] : ( ( human @ X_V ) => "
            "( ? [P_P: $i > $o] : ( ( pos @ P_P ) & ( P_P @ X_V ) ) ) ) ) ))." in problem)
    assert ("thf(goal, conjecture, ( ( ? [P_P: $i > $o] : ( ( pos @ P_P ) & "
            "( P_P @ socrates ) ) ) ))." in problem)


def _formulas_of(thf_problem):
    """The formula of every axiom and of the conjecture, without the names."""
    out = []
    for line in thf_problem.splitlines():
        if line.startswith("thf(") and (", axiom, " in line or ", conjecture, " in line):
            out.append(line.split(", ", 2)[2])
    return out


def test_a_sorted_problem_is_the_unsorted_one_with_the_facts_as_assumptions():
    """The same problem written by hand: every sorted binder as a guarded one, every
    sorted constant as the plain one, and ``∃x0 Human(x0)`` and ``Human(socrates)`` as
    two more assumptions. The two texts differ in the names of those two axioms alone."""
    by_hand = to_thf_to(
        TO("∃P (Pos(P) ∧ P(socrates))"),
        assumptions=[
            Quantifier("∃", Variable("x0"), Atom("Human", (Variable("x0"),))),
            Atom("Human", (Constant("socrates"),)),
            TO("∀x (Human(x) → ∃P (Pos(P) ∧ P(x)))"),
        ])
    sorted_problem = to_thf_to(TOS(GOAL), assumptions=[TOS(ASSUMPTION)])
    assert _formulas_of(sorted_problem) == _formulas_of(by_hand)
    declarations = [line for line in sorted_problem.splitlines() if ", type, " in line]
    assert declarations == [line for line in by_hand.splitlines() if ", type, " in line]


def test_an_unsorted_problem_gets_no_sort_fact():
    for text in (to_isabelle_to(TO("∀P (Pos(P) → P(a))"), assumptions=[TO("Pos(G)")]),
                 to_thf_to(TO("∀P (Pos(P) → P(a))"), assumptions=[TO("Pos(G)")])):
        assert "nonempty_sort" not in text and "sort_member" not in text


def test_a_sort_that_occurs_through_a_constant_alone_is_declared_and_not_empty():
    theory = to_isabelle_to(TOS("Pos(G) → G(alice:Human)"))
    assert 'consts Human :: "i \\<Rightarrow> bool"' in theory
    assert "nonempty_sort0" in theory and "sort_member0" in theory


def test_two_sorts_and_two_sorted_constants_are_numbered_in_order_of_occurrence():
    problem = to_thf_to(TOS("∀x:Human ∃y:City (Lives(x, y) ∧ Lives(bob:Human, rome:City))"))
    assert "thf(nonempty_sort0, axiom, ( ( ? [X0_V: $i] : ( human @ X0_V ) ) ))." in problem
    assert "thf(nonempty_sort1, axiom, ( ( ? [X1_V: $i] : ( city @ X1_V ) ) ))." in problem
    assert "thf(sort_member0, axiom, ( ( human @ bob ) ))." in problem
    assert "thf(sort_member1, axiom, ( ( city @ rome ) ))." in problem


def test_a_sorted_second_order_formula_goes_through_the_same_writers():
    """Second-order syntax is part of what the third-order writers read."""
    problem = to_thf_to(SOS("∃P ∀x:S (P(x) ↔ Q(x))"))
    assert "thf(nonempty_sort0, axiom, ( ( ? [X0_V: $i] : ( s @ X0_V ) ) ))." in problem
    for writer, named in ((to_thf_so, "to_thf_to"), (to_isabelle_so, "to_isabelle_to")):
        with pytest.raises(NotImplementedError, match=named):
            writer(SOS("∃P ∀x:S (P(x) ↔ Q(x))"))


@pytest.mark.parametrize("writer", [to_isabelle_to, to_thf_to])
def test_a_bound_predicate_named_like_a_sort_is_refused(writer):
    """After the rewriting the guard of ``∀x:Human`` is the atom ``Human(x)``, which a
    quantifier over ``Human`` would capture."""
    with pytest.raises(NotImplementedError, match="name of a sort"):
        writer(TOS("∀Human ∀x:Human Human(x)"))
    # in an assumption as well
    with pytest.raises(NotImplementedError, match="name of a sort"):
        writer(TOS("Pos(G)"), assumptions=[TOS("∃Human ∃x:Human Human(x)")])


def test_satisfies_to_takes_an_assignment_under_a_sorted_binder():
    assert satisfies_to(TOS("∃y:Human (P(y) ∧ G(x))"), Structure(
        (0, 1, 2), sorts={"Human": {0, 1}},
        predicates={("G", 1): {(0,)}, ("P", 1): {(1,)}}), {"x": 0}) is True


# ---------------------------------------------------------------------------
# Live: the theories build with a local Isabelle
# ---------------------------------------------------------------------------

@_isa_live
@_isa
def test_live_the_membership_of_a_sorted_constant_closes_the_goal():
    """Every human has a positive property, and ``socrates:Human`` is a human: the
    proof uses the assumption and the fact ``sort_member0``."""
    theory = to_isabelle_to(TOS(GOAL), name="TO_Sorted", assumptions=[TOS(ASSUMPTION)],
                            proof="using assumption1 sort_member0 by blast")
    result = check_theory(theory, "TO_Sorted", session_timeout=240)
    assert result.ok, result.output[-2000:]


@_isa_live
@_isa
def test_live_a_sort_is_not_empty():
    """``∀P (∀x:Human P(x) → ∃x:Human P(x))`` needs a human; ``nonempty_sort0`` is one."""
    theory = to_isabelle_to(TOS("∀P (∀x:Human P(x) → ∃x:Human P(x))"),
                            name="TO_Sorted_Witness", proof="using nonempty_sort0 by blast")
    result = check_theory(theory, "TO_Sorted_Witness", session_timeout=240)
    assert result.ok, result.output[-2000:]
