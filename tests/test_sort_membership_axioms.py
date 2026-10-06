"""``sort_membership_axioms`` / ``sort_axioms``: a sorted constant is in its sort.

The guard reduction ``to_fol`` writes ``∀x:S φ`` as ``∀x (S(x) → φ)`` and ``c:S`` as
``c``; ``nonempty_sort_axioms`` adds ``∃x S(x)``. What was missing is the fact that
the annotation of a constant states: ``S(c)``. These tests pin the function that
returns it, and check on Z3 -- over the plain ``to_fol`` images, so that no
backend's own handling of sorted input is involved -- that the three families of
background facts together decide what the definition says.

Hand-derived expectations (one universe; a sort is the non-empty extension of the
unary predicate of its name; ``c:S`` denotes an element of ``S``; an unsorted
constant and a function value may be any element):

* ``∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)`` is VALID: socrates is a Human.
* ``∀x:Human Mortal(x) ⊢ Mortal(socrates)`` is NOT: universe {0, 1}, Human = {0},
  Mortal = {0}, socrates = 1.
* ``⊢ Mortal(socrates:Human)`` is NOT: universe {0}, Human = {0}, Mortal = {},
  socrates = 0. The membership fact is a premise, never the conclusion's work.
* ``P(carl:A), Q(carl:B) ⊢ ∃x:A Q(x)`` is VALID: carl is in A (and in B), and Q(carl).
* ``P(carl), Q(carl:A) ⊢ ∃x:A P(x)`` is VALID: one constant, in A by its sorted
  occurrence.
* ``∀x:Human ¬Evil(x) ⊢ ¬Evil(socrates:Human)`` is VALID, and the annotation
  under the negation still yields the POSITIVE fact ``Human(socrates)``.
"""

from unicode_fol_kit import api
from unicode_fol_kit.atp import z3_models
from unicode_fol_kit.fol import nonempty_sort_axioms, sort_axioms, sort_membership_axioms, to_fol
from unicode_fol_kit.fol._msfl_nodes import SortedConstant, SortedQuantifier
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Function, Implies, Not, Quantifier, Variable

X = Variable("x")
SOCRATES = SortedConstant("socrates", "Human")
ALL_HUMANS_MORTAL = SortedQuantifier("∀", X, "Human", Atom("Mortal", [X]))


def entailed(premises, conclusion):
    """Z3 on the guard images plus ``sort_axioms`` as premises. The images hold no
    sorted node, so ``z3_models.is_valid`` adds nothing of its own."""
    background = list(sort_axioms(*premises, conclusion))
    hypotheses = background + [to_fol(p) for p in premises]
    goal = to_fol(conclusion)
    if not hypotheses:
        return z3_models.is_valid(goal)
    conjunction = hypotheses[0]
    for h in hypotheses[1:]:
        conjunction = And(conjunction, h)
    return z3_models.is_valid(Implies(conjunction, goal))


# ---------------------------------------------------------------------------------------------
# the function
# ---------------------------------------------------------------------------------------------
def test_one_atom_per_sorted_constant_over_the_plain_constant():
    assert sort_membership_axioms(Atom("Mortal", [SOCRATES])) == (Atom("Human", [Constant("socrates")]),)


def test_no_sorted_constant_gives_no_axiom():
    assert sort_membership_axioms(ALL_HUMANS_MORTAL, Atom("Mortal", [Constant("socrates")])) == ()
    assert sort_membership_axioms() == ()


def test_first_occurrence_order_and_no_duplicates_across_sentences():
    plato = SortedConstant("plato", "Greek")
    axioms = sort_membership_axioms(Atom("P", [plato]), Atom("Q", [SOCRATES, plato]), Atom("R", [SOCRATES]))
    assert axioms == (Atom("Greek", [Constant("plato")]), Atom("Human", [Constant("socrates")]))


def test_a_constant_with_two_sorts_gets_both_atoms():
    axioms = sort_membership_axioms(Atom("P", [SortedConstant("carl", "A")]), Atom("Q", [SortedConstant("carl", "B")]))
    assert axioms == (Atom("A", [Constant("carl")]), Atom("B", [Constant("carl")]))


def test_a_sorted_constant_is_found_inside_a_function_under_a_negation_and_a_binder():
    buried = SortedQuantifier("∀", X, "Greek", Not(Atom("R", [X, Function("f", [SOCRATES])])))
    assert sort_membership_axioms(buried) == (Atom("Human", [Constant("socrates")]),)


def test_the_atom_prints_as_text_the_parser_reads_back():
    (axiom,) = sort_membership_axioms(Atom("Mortal", [SOCRATES]))
    assert axiom.to_unicode_str() == "Human(socrates)"
    assert api.parse_any("Human(socrates)").formula == axiom


def test_sort_axioms_is_non_emptiness_followed_by_membership():
    sentences = (ALL_HUMANS_MORTAL, Atom("Mortal", [SOCRATES]))
    assert sort_axioms(*sentences) == nonempty_sort_axioms(*sentences) + sort_membership_axioms(*sentences)
    assert [a.to_unicode_str() for a in sort_axioms(*sentences)] == ["∃x0 Human(x0)", "Human(socrates)"]


def test_nonempty_sort_axioms_itself_is_unchanged():
    """Three modal routes read the sort NAME off this function's ``∃x S(x)`` shape."""
    (axiom,) = nonempty_sort_axioms(Atom("Mortal", [SOCRATES]))
    assert isinstance(axiom, Quantifier) and axiom.type == "∃"
    assert axiom.formula.predicate == "Human" and axiom.formula.args == (axiom.variable,)


# ---------------------------------------------------------------------------------------------
# what the three families decide together (hand-derived, see the module docstring)
# ---------------------------------------------------------------------------------------------
def test_a_sorted_constant_instantiates_a_sorted_universal():
    assert entailed([ALL_HUMANS_MORTAL], Atom("Mortal", [SOCRATES])) is True


def test_an_unsorted_constant_does_not():
    assert entailed([ALL_HUMANS_MORTAL], Atom("Mortal", [Constant("socrates")])) is False


def test_membership_is_a_premise_and_proves_nothing_about_the_constant():
    assert entailed([], Atom("Mortal", [SOCRATES])) is False
    assert entailed([], Not(Atom("Mortal", [SOCRATES]))) is False


def test_without_the_membership_atom_the_valid_entailment_has_a_countermodel():
    """The defect this function closes, kept as a control: non-emptiness alone is not enough."""
    hypotheses = And(nonempty_sort_axioms(ALL_HUMANS_MORTAL)[0], to_fol(ALL_HUMANS_MORTAL))
    assert z3_models.is_valid(Implies(hypotheses, to_fol(Atom("Mortal", [SOCRATES])))) is False


def test_a_constant_with_two_sorts_is_in_both():
    carl_a, carl_b = SortedConstant("carl", "A"), SortedConstant("carl", "B")
    premises = [Atom("P", [carl_a]), Atom("Q", [carl_b])]
    assert entailed(premises, SortedQuantifier("∃", X, "A", Atom("Q", [X]))) is True
    assert entailed(premises, SortedQuantifier("∃", X, "B", Atom("P", [X]))) is True


def test_a_sorted_and_an_unsorted_occurrence_are_one_constant():
    premises = [Atom("P", [Constant("carl")]), Atom("Q", [SortedConstant("carl", "A")])]
    assert entailed(premises, SortedQuantifier("∃", X, "A", Atom("P", [X]))) is True


def test_the_annotation_under_a_negation_still_states_the_positive_fact():
    premise = SortedQuantifier("∀", X, "Human", Not(Atom("Evil", [X])))
    assert entailed([premise], Not(Atom("Evil", [SOCRATES]))) is True


def test_a_sorted_constant_witnesses_its_sort():
    assert entailed([], SortedQuantifier("∃", X, "Human", Atom("=", [X, SOCRATES]))) is True


def test_two_sorted_constants_of_one_sort_need_not_be_equal():
    assert entailed([], Atom("=", [SortedConstant("anna", "S"), SortedConstant("bert", "S")])) is False
