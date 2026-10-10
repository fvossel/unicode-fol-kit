"""``hol.ho_modal`` on second-order modal formulas and on sorted individuals.

The shallow embedding was written for third-order modal logic. Two kinds of input
reach it from the modes next to that one:

- a SECOND-ORDER modal formula (``MSFLParser(second_order=True, modal=True)``), which
  is third-order modal syntax without a predicate in argument position; its binders
  may share a name at two arities, since the arity is read per binder there;
- a MANY-SORTED formula, at second or third order, which is written as the unsorted
  formula plus two families of axioms valid at every world: ``nonempty_sort<i>`` and
  ``sort_member<i>``.

The sorted theory is checked against the same theory written by hand, text for text.
The live tests build the theories with a local Isabelle.
"""

import pytest

from unicode_logic_kit import (
    HoAxiom, HoGoal, MSFLParser, isabelle_ho_modal_theory, qml_is_valid,
    to_isabelle_ho_modal, to_thf_ho_modal,
)
from unicode_logic_kit.fol.nodes import Atom, Constant, Quantifier, Variable
from unicode_logic_kit.hol.isabelle_runner import check_theory, isabelle_available

SOM = MSFLParser(second_order=True, modal=True).parse
SOMS = MSFLParser(second_order=True, modal=True, many_sorted=True).parse
TOM = MSFLParser(third_order=True, modal=True).parse
TOMS = MSFLParser(third_order=True, modal=True, many_sorted=True).parse

_isa = pytest.mark.skipif(not isabelle_available(), reason="no local Isabelle installation")
_isa_live = pytest.mark.isabelle_live

NITPICK = "nitpick [user_axioms, expect = genuine]\n  oops"

#: ``∃x0 Human(x0)`` and ``Human(socrates)``: the two facts about the sort ``Human``
#: with the sorted constant ``socrates:Human``.
NONEMPTY_HUMAN = Quantifier("∃", Variable("x0"), Atom("Human", (Variable("x0"),)))
SOCRATES_IS_HUMAN = Atom("Human", (Constant("socrates"),))


# ---------------------------------------------------------------------------
# Second-order modal formulas
# ---------------------------------------------------------------------------

def test_a_propositional_and_a_binary_binder_of_one_name():
    """``∀P`` over a proposition and ``∃P`` over a binary relation in one formula: each
    binder is typed at its own arity."""
    theory = to_isabelle_ho_modal(SOM("(∀P (□P → P)) ∧ ∃P P(a, b)"), frame="T")
    assert "(mall (\\<lambda>P::sigma. (mimp (mbox P) P)))" in theory
    assert "(mex (\\<lambda>P::i \\<Rightarrow> i \\<Rightarrow> sigma. (P a b)))" in theory
    assert 'axiomatization where R_refl: "\\<forall>x. R x x"' in theory
    # a bound predicate is not a constant of the theory
    assert "consts P ::" not in theory


def test_a_second_order_modal_problem_in_thf():
    problem = to_thf_ho_modal(SOM("∀P (□P → P)"), frame="T")
    assert ("thf(goal, conjecture, ( mvalid @ ( ^ [W0: mu] : ( ! [P_P: mu > $o] : "
            "( ( mimp @ ( mbox @ P_P ) @ P_P ) @ W0 ) ) ) ))." in problem)
    assert "thf(frame_refl, axiom, ( ! [W: mu] : ( r @ W @ W ) ))." in problem


def test_a_predicate_quantifier_is_not_guarded_by_existence():
    """Under varying domains the individual binder is guarded and the predicate
    binder is not: a property does not come and go with a world's domain."""
    theory = to_isabelle_ho_modal(SOM("∀P ∃x P(x)"), mode="varying")
    assert "(mall (\\<lambda>P::i \\<Rightarrow> sigma. (mexists (\\<lambda>x::i. (P x)))))" in theory


# ---------------------------------------------------------------------------
# Sorted individuals
# ---------------------------------------------------------------------------

def test_the_facts_about_a_sort_are_axioms_valid_at_every_world():
    theory = isabelle_ho_modal_theory(
        "Sorted", (), [HoGoal("g", SOMS("□∀x:Human Mortal(x) → □Mortal(socrates:Human)"))])
    assert 'consts Human :: "i \\<Rightarrow> sigma"' in theory
    assert ('axiomatization where nonempty_sort0: '
            '"mvalid (mex (\\<lambda>x0::i. (Human x0)))"' in theory)
    assert 'axiomatization where sort_member0: "mvalid (Human socrates)"' in theory
    assert ('theorem g: "mvalid (mimp (mbox (mall (\\<lambda>x::i. (mimp (Human x) '
            '(Mortal x))))) (mbox (Mortal socrates)))"' in theory)


def test_under_varying_domains_the_witness_of_a_sort_exists_at_the_world():
    """The witness goes through the guarded binder like any ``∃x``; the membership of
    a constant is not guarded."""
    theory = isabelle_ho_modal_theory(
        "Sorted", (), [HoGoal("g", SOMS("∀x:Human Mortal(x) → ∃x:Human Mortal(x)"))],
        mode="varying")
    assert ('axiomatization where nonempty_sort0: '
            '"mvalid (mexists (\\<lambda>x0::i. (Human x0)))"' in theory)
    problem = to_thf_ho_modal(SOMS("Mortal(socrates:Human)"), mode="varying")
    assert ("thf(nonempty_sort0, axiom, ( mvalid @ ( ^ [W0: mu] : ( ? [X0_V: $i] : "
            "( ( existsat @ X0_V @ W0 ) & ( ( human @ X0_V ) @ W0 ) ) ) ) ))." in problem)
    assert "thf(sort_member0, axiom, ( mvalid @ ( human @ socrates ) ))." in problem


def test_a_sort_known_through_a_constant_alone_brings_the_domain_vocabulary():
    """``□Mortal(socrates:Human)`` has no quantifier of its own. The fact that
    ``Human`` is not empty has one, and under varying domains it needs ``existsAt``."""
    theory = to_isabelle_ho_modal(SOMS("□Mortal(socrates:Human)"), mode="varying")
    assert "consts existsAt ::" in theory
    assert "abbreviation mexists ::" in theory
    assert "axiomatization where nonempty_dom:" in theory
    constant = to_isabelle_ho_modal(SOMS("□Mortal(socrates:Human)"))
    assert "existsAt" not in constant


@pytest.mark.parametrize("mode", ["constant", "varying", "increasing", "decreasing"])
def test_a_sorted_theory_is_the_unsorted_one_with_the_facts_as_axioms(mode):
    """Written by hand: the sorted binder as a guarded one, the sorted constant as the
    plain one, and the two facts as axioms under the names the writer gives them."""
    axiom = "∀P (Pos(P) → □∃x:Human P(x))"
    goal = "□∀x:Human Mortal(x) → □Mortal(socrates:Human)"
    by_hand = isabelle_ho_modal_theory(
        "Sorted",
        [HoAxiom("nonempty_sort0", NONEMPTY_HUMAN),
         HoAxiom("sort_member0", SOCRATES_IS_HUMAN),
         HoAxiom("A1", TOM("∀P (Pos(P) → □∃x (Human(x) ∧ P(x)))"))],
        [HoGoal("g", TOM("□∀x (Human(x) → Mortal(x)) → □Mortal(socrates)"), "by blast")],
        frame="S4", mode=mode)
    written = isabelle_ho_modal_theory(
        "Sorted", [HoAxiom("A1", TOMS(axiom))], [HoGoal("g", TOMS(goal), "by blast")],
        frame="S4", mode=mode)
    assert written == by_hand


@pytest.mark.parametrize("mode", ["constant", "varying"])
def test_a_sorted_thf_problem_is_the_unsorted_one_with_the_facts_as_axioms(mode):
    by_hand = to_thf_ho_modal(
        TOM("□∀x (Human(x) → Mortal(x)) → □Mortal(socrates)"), frame="S4", mode=mode,
        axioms=[HoAxiom("nonempty_sort0", NONEMPTY_HUMAN),
                HoAxiom("sort_member0", SOCRATES_IS_HUMAN),
                HoAxiom("A1", TOM("∀P (Pos(P) → □∃x (Human(x) ∧ P(x)))"))])
    written = to_thf_ho_modal(
        TOMS("□∀x:Human Mortal(x) → □Mortal(socrates:Human)"), frame="S4", mode=mode,
        axioms=[HoAxiom("A1", TOMS("∀P (Pos(P) → □∃x:Human P(x))"))])
    assert written == by_hand


def test_an_unsorted_theory_gets_no_sort_fact():
    theory = isabelle_ho_modal_theory(
        "Plain", [HoAxiom("A1", TOM("∀P (Pos(P) → □Pos(P))"))],
        [HoGoal("g", TOM("∀x (Pos(G) → □□Pos(G))"))])
    problem = to_thf_ho_modal(TOM("∀x (Pos(G) → □□Pos(G))"))
    for text in (theory, problem):
        assert "nonempty_sort" not in text and "sort_member" not in text


def test_a_goal_stated_raw_stands_next_to_sorted_axioms():
    theory = isabelle_ho_modal_theory(
        "Raw", [HoAxiom("A1", SOMS("∀x:Human □Mortal(x)"))],
        [HoGoal("consistent", statement="True", proof="by simp")])
    assert "nonempty_sort0" in theory and "sort_member" not in theory
    assert 'theorem consistent: "True"' in theory


@pytest.mark.parametrize("taken", ["nonempty_sort0", "sort_member0"])
def test_an_axiom_or_goal_named_like_a_fact_about_a_sort_is_refused(taken):
    # The problem ∀x:Human Mortal(x) ⊢ Mortal(socrates:Human) states nonempty_sort0 and
    # sort_member0 itself, so a second statement of one of those names is a duplicate.
    axiom = SOMS("∀x:Human Mortal(x)")
    goal = SOMS("Mortal(socrates:Human)")
    with pytest.raises(ValueError, match=taken):
        isabelle_ho_modal_theory("T", [HoAxiom(taken, axiom)], [HoGoal("g", goal)])
    with pytest.raises(ValueError, match=taken):
        isabelle_ho_modal_theory("T", [HoAxiom("A1", axiom)], [HoGoal(taken, goal)])
    with pytest.raises(ValueError, match=taken):
        isabelle_ho_modal_theory(
            "T", [HoAxiom("A1", axiom)],
            [HoGoal("g", goal), HoGoal(taken, statement="True", proof="by simp")])
    with pytest.raises(ValueError, match=taken):
        to_thf_ho_modal(goal, axioms=[HoAxiom(taken, axiom)])


def test_such_a_name_is_free_where_the_problem_states_no_fact_of_it():
    # One sort and no sorted constant: nonempty_sort0 is stated and sort_member0 is not.
    theory = isabelle_ho_modal_theory(
        "T", [HoAxiom("sort_member0", SOMS("∀x:Human Mortal(x)"))], ())
    assert theory.count("axiomatization where nonempty_sort0:") == 1
    assert theory.count("axiomatization where sort_member0:") == 1
    # An unsorted problem states neither.
    unsorted = isabelle_ho_modal_theory(
        "T", [HoAxiom("nonempty_sort0", SOM("∀P (□P → P)"))], ())
    assert unsorted.count("axiomatization where nonempty_sort0:") == 1


@pytest.mark.parametrize("writer", [
    lambda formula: to_isabelle_ho_modal(formula),
    lambda formula: to_thf_ho_modal(formula),
    lambda formula: isabelle_ho_modal_theory("T", [HoAxiom("A", formula)], ()),
])
def test_a_bound_predicate_named_like_a_sort_is_refused(writer):
    with pytest.raises(NotImplementedError, match="name of a sort"):
        writer(TOMS("∃Being □∀x:Being Being(x)"))


# ---------------------------------------------------------------------------
# Live: the theories build with a local Isabelle
# ---------------------------------------------------------------------------
#
# The proof texts were written by hand and confirmed on Isabelle2025-2. Two goals
# need a witness that the automation does not find on its own, a proposition built
# from another one; their proofs name it.

def _build(theory, name):
    result = check_theory(theory, name, session_timeout=240)
    assert result.ok, f"{name} did not build (exit {result.exit_code}):\n{result.output[-2000:]}"


@_isa_live
@_isa
def test_live_seeing_itself_is_a_theorem_on_reflexive_frames_and_refuted_without():
    """``∀P (□P → P)`` says of a world that it sees itself (the Kripke evaluator checks
    that on every small frame, tests/test_second_order_modal_semantics.py). Isabelle
    agrees from the other side: a theorem in T, a countermodel in K."""
    formula = SOM("∀P (□P → P)")
    _build(isabelle_ho_modal_theory(
        "SomRefl", (), [HoGoal("refl", formula, proof="using R_refl by blast")],
        frame="T"), "SomRefl")
    _build(isabelle_ho_modal_theory(
        "SomK", (), [HoGoal("refl", formula, proof=NITPICK, kind="lemma"),
                     HoGoal("trans", SOM("∀P (□P → □□P)"), proof=NITPICK, kind="lemma")],
        frame="K"), "SomK")


@_isa_live
@_isa
def test_live_the_frame_condition_follows_from_the_formula():
    """The other direction of the correspondence: with ``∀P (□P → P)`` valid, the
    relation is reflexive. The instance is P = the successors of the world."""
    _build(isabelle_ho_modal_theory(
        "SomCorr", [HoAxiom("A", SOM("∀P (□P → P)"))],
        [HoGoal("reflexive", statement="\\<forall>w. R w w", proof="by (metis A)")],
        frame="K"), "SomCorr")


_COMPLEMENT_PROOF = "\n".join([
    "proof (intro allI)",
    "    fix w P",
    '    show "\\<exists>Q. \\<forall>v. R w v \\<longrightarrow> '
    '(P v \\<longleftrightarrow> \\<not> Q v)"',
    '      by (rule exI[of _ "\\<lambda>v. \\<not> P v"]) simp',
    "  qed",
])
_WORLD_PROPOSITION_PROOF = "\n".join([
    "proof (intro allI)",
    "    fix w",
    '    show "\\<exists>P. P w \\<and> (\\<forall>Q. Q w \\<longrightarrow> '
    '(\\<forall>v. R w v \\<longrightarrow> (P v \\<longrightarrow> Q v)))"',
    '      by (rule exI[of _ "\\<lambda>v. v = w"]) simp',
    "  qed",
])


@_isa_live
@_isa
def test_live_two_theorems_with_a_proposition_as_witness():
    """``∀P ∃Q □(P ↔ ¬Q)``: Q is the complement of P. ``∃P (P ∧ ∀Q (Q → □(P → Q)))``:
    P is the proposition true at this world alone, so whatever holds here holds
    wherever P does. The bounded search finds no countermodel to either."""
    _build(isabelle_ho_modal_theory(
        "SomWitness", (),
        [HoGoal("complement", SOM("∀P ∃Q □(P ↔ ¬Q)"), proof=_COMPLEMENT_PROOF),
         HoGoal("world_proposition", SOM("∃P (P ∧ ∀Q (Q → □(P → Q)))"),
                proof=_WORLD_PROPOSITION_PROOF)],
        frame="K"), "SomWitness")


MEMBER = "□∀x:Human Mortal(x) → □Mortal(socrates:Human)"
WITNESS = "∀x:Human Mortal(x) → ∃x:Human Mortal(x)"


@pytest.mark.parametrize("mode, member_valid", [("constant", True), ("varying", False)])
def test_the_first_order_route_on_the_two_sorted_goals(mode, member_valid):
    """What the live test below is measured against, decided by ``qml_is_valid`` on the
    same two texts read at first order.

    ``∀x:Human`` ranges over the humans that EXIST at the world, under varying domains.
    A constant is a rigid designator that may lie outside the domain of a world, so
    ``socrates:Human`` is a human there without being one of those, and the first goal
    is valid with constant domains and not with varying ones. The second goal needs a
    witness of the sort, which exists at the world in both regimes."""
    first_order = MSFLParser(modal=True, many_sorted=True).parse
    assert qml_is_valid(first_order(MEMBER), mode=mode) is member_valid
    assert qml_is_valid(first_order(WITNESS), mode=mode) is True


@_isa_live
@_isa
@pytest.mark.parametrize("mode, member_valid", [("constant", True), ("varying", False)])
def test_live_the_facts_about_a_sort_prove_what_the_first_order_route_calls_valid(
        mode, member_valid):
    """The higher-order theory proves the two goals where ``qml_is_valid`` calls them
    valid and has a countermodel where it does not; a predicate quantifier over the
    sorted individuals goes through in both regimes."""
    name = f"Sorted_{mode}"
    _build(isabelle_ho_modal_theory(name, (), [
        HoGoal("member", SOMS(MEMBER), kind="theorem" if member_valid else "lemma",
               proof="using sort_member0 by blast" if member_valid else NITPICK),
        HoGoal("witness", SOMS(WITNESS), proof="using nonempty_sort0 by blast"),
        HoGoal("second_order", SOMS("∀P (∀x:Human P(x) → ∃x:Human P(x))"),
               proof="using nonempty_sort0 by blast"),
    ], frame="K", mode=mode), name)


@_isa_live
@_isa
def test_live_third_order_modal_over_sorted_individuals():
    _build(isabelle_ho_modal_theory(
        "TomSorted", [HoAxiom("A1", TOMS("∀P (Pos(P) → □Pos(P))"))],
        [HoGoal("twice", TOMS("∀x:Being (Pos(G) → □□Pos(G))"), proof="using A1 by blast"),
         HoGoal("member", TOMS("∀x:Being G(x) → G(zeus:Being)"),
                proof="using sort_member0 by blast")],
        frame="K"), "TomSorted")
