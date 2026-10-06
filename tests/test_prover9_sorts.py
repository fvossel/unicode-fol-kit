r"""The Prover9 problem writer asks the many-sorted question, and writes it so Prover9 reads it.

A sort ``S`` is the extension of the unary predicate ``S`` (one symbol) and is never
empty; a sorted constant ``c:S`` denotes an element of ``S``; a constant written with
two sorts lies in both; ``c:S`` here and a plain ``c`` there are ONE constant. A sorted
quantifier ``∀x:S φ`` is ``∀x (S(x) → φ)``. The writer lowers a sorted node to the plain
guard and the plain constant, which forgets that ``c`` is in ``S``, so it states that
fact itself, as one more assumption ``S(c)`` per sorted constant, next to the
non-emptiness assumption ``∃x S(x)`` per sort. Without it ``∀x:Human Mortal(x) ⊢
Mortal(socrates:Human)`` is not proved: the plain text has the countermodel in which
``socrates`` is no ``Human``.

The atom ``S(c)`` must be about the token the PREMISES use for the constant, and the
writer renames constants Prover9 would misread (an upper-case ``Gaseous`` becomes
``gaseous``, a digit-leading ``2008wins`` becomes ``s2008wins``, a non-ASCII name is
transliterated). A raw-built atom would be about another symbol and the proof would
silently fail, so the atoms are built from the SANITISED formulas, and a sorted
constant is renamed exactly like a plain constant of that name.

Every expected text below is derived by hand from those rules. The live tests, which
run the real Prover9 (natively, or inside WSL with ``$UFK_PROVER9_WSL=1``) and skip with
a reason where there is none, decide the fourteen problems of the sorted-constant
matrix: the verdict of each is derived by hand from the definition above and written
next to the problem, and Prover9 must prove exactly the valid and the unsatisfiable
ones.
"""

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.prover9_entailment import (
    _sanitize_for_prover9, generate_prover9_input_with_mapping,
)
from unicode_fol_kit.atp.protocol import Prover9Backend, get_backend
from unicode_fol_kit.fol._msfl_nodes import SortedConstant, SortedQuantifier
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Function, Variable

x = Variable("x")


def _assumptions_and_goals(text):
    """The formula lines of the ``assumptions`` list and of the ``goals`` list of a written problem."""
    lines = [line.strip() for line in text.splitlines()]
    assumptions = lines[lines.index("formulas(assumptions).") + 1:]
    assumptions = assumptions[:assumptions.index("end_of_list.")]
    goals = lines[lines.index("formulas(goals).") + 1:]
    goals = goals[:goals.index("end_of_list.")]
    return assumptions, goals


def _written(premises, conclusion):
    text, mapping = generate_prover9_input_with_mapping(premises, conclusion)
    return (*_assumptions_and_goals(text), mapping)


# --------------------------------------------------------------------------- #
# The membership line names the token the premises use.
# --------------------------------------------------------------------------- #

def test_a_sorted_constant_of_the_conclusion_is_asserted_to_be_in_its_sort():
    # ∀x:Human Mortal(x) ⊢ Mortal(socrates:Human). Hand-derived: the premise is the
    # guarded universal; the sort Human is non-empty; socrates is in Human, written as an
    # ASSUMPTION (Prover9 negates the goal itself, and a membership under that negation
    # would be something to prove); the goal is the plain Mortal(socrates).
    assumptions, goals, _ = _written(
        [SortedQuantifier("∀", x, "Human", Atom("Mortal", [x]))],
        Atom("Mortal", [SortedConstant("socrates", "Human")]))
    assert assumptions == ["(all X (Human(X) -> Mortal(X))).", "(exists X0 Human(X0)).",
                           "Human(socrates)."]
    assert goals == ["Mortal(socrates)."]


def test_an_upper_case_sorted_constant_has_the_token_of_its_premise_in_the_membership_line():
    # Gaseous:Phase. Prover9 reads a bare Gaseous as a variable, so the writer spells the
    # constant `gaseous`; the membership atom must say Phase(gaseous), not Phase(Gaseous)
    # (a variable: "everything is a Phase") and not Phase("Gaseous") (another symbol).
    assumptions, goals, mapping = _written(
        [Atom("P", [SortedConstant("Gaseous", "Phase")])], Atom("Q", [Constant("c")]))
    assert assumptions == ["P(gaseous).", "(exists X0 Phase(X0)).", "Phase(gaseous)."]
    assert goals == ["Q(c)."]
    assert mapping.constants == {"Gaseous": "gaseous"}


def test_a_digit_leading_sorted_constant_has_the_token_of_its_plain_twin():
    # 2008wins is no legal Prover9 name start for this kit's reader; the writer spells it
    # s2008wins. The plain occurrence (a premise) and the sorted one (the conclusion) are
    # ONE constant: both say s2008wins, and so does the membership atom. (The sorted
    # occurrence used to keep its raw name, so the conclusion talked about `2008wins`.)
    assumptions, goals, mapping = _written(
        [Atom("Mortal", [Constant("2008wins")])], Atom("Q", [SortedConstant("2008wins", "Human")]))
    assert assumptions == ["Mortal(s2008wins).", "(exists X0 Human(X0)).", "Human(s2008wins)."]
    assert goals == ["Q(s2008wins)."]
    assert mapping.mapping["2008wins"] == "s2008wins"


def test_a_constant_with_two_sorts_gets_one_membership_atom_per_sort_and_one_token():
    # P(carl:A), Q(carl:B): carl is in A and in B.
    assumptions, goals, _ = _written(
        [Atom("P", [SortedConstant("carl", "A")]), Atom("Q", [SortedConstant("carl", "B")])],
        Atom("R", [Constant("c")]))
    assert assumptions == ["P(carl).", "Q(carl).", "(exists X0 A(X0)).", "(exists X1 B(X1)).",
                           "A(carl).", "B(carl)."]
    assert goals == ["R(c)."]


def test_a_constant_sorted_here_and_plain_there_is_one_constant_in_its_sort():
    # P(carl) and Q(carl:A): one constant carl, and it is in A.
    assumptions, _, _ = _written(
        [Atom("P", [Constant("carl")]), Atom("Q", [SortedConstant("carl", "A")])],
        Atom("R", [Constant("c")]))
    assert assumptions == ["P(carl).", "Q(carl).", "(exists X0 A(X0)).", "A(carl)."]


def test_a_non_ascii_sorted_constant_is_transliterated_like_its_plain_twin():
    # świątek -> u015bwiu0105tek: one token for the premise and for the membership line.
    assumptions, goals, _ = _written(
        [Atom("P", [Constant("świątek")])], Atom("Q", [SortedConstant("świątek", "Human")]))
    assert assumptions == ["P(u015bwiu0105tek).", "(exists X0 Human(X0)).", "Human(u015bwiu0105tek)."]
    assert goals == ["Q(u015bwiu0105tek)."]


def test_two_constants_that_transliterate_alike_stay_two_symbols_when_one_is_sorted():
    # θ transliterates to `theta`, which is also the legal name of the constant `theta`.
    # The writer keeps the two apart for plain constants (theta, theta2); the sorted θ
    # used to skip that renaming and was written `theta` too: ONE symbol for two.
    assumptions, goals, mapping = _written(
        [Atom("P", [Constant("theta")])], Atom("Q", [SortedConstant("θ", "Human")]))
    assert assumptions == ["P(theta).", "(exists X0 Human(X0)).", "Human(theta2)."]
    assert goals == ["Q(theta2)."]
    assert mapping.mapping["θ"] == "theta2" and mapping.mapping["theta"] == "theta"


def test_a_sorted_constant_under_a_function_and_in_the_conclusion_is_covered():
    assumptions, goals, _ = _written([], Atom("Q", [Function("f", [SortedConstant("Eve", "Human")])]))
    assert assumptions == ["(exists X0 Human(X0)).", "Human(eve)."]
    assert goals == ["Q(f(eve))."]


def test_a_renamed_constant_never_takes_the_name_of_a_sort():
    # A sort name is written as it is (it is the guard predicate), and Prover9 keeps one
    # symbol per spelling, so the constant `Human` (renamed to a lower-case token) must
    # not become `human` when a sort of that name is in the problem: it becomes human2.
    assumptions, goals, mapping = _written(
        [SortedQuantifier("∀", x, "human", Atom("P", [x, Constant("Human")]))],
        Atom("Q", [SortedConstant("Human", "human")]))
    assert assumptions == ["(all X (human(X) -> P(X, human2))).", "(exists X0 human(X0)).",
                           "human(human2)."]
    assert goals == ["Q(human2)."]
    assert mapping.constants == {"Human": "human2"}


def test_the_sanitiser_renames_a_sorted_constant_exactly_like_a_plain_one():
    for name, token in (("Gaseous", "gaseous"), ("2008wins", "s2008wins"), ("świątek", "u015bwiu0105tek"),
                        ("_x", "c_x"), ("carl", "carl")):
        (plain, sorted_), mapping = _sanitize_for_prover9(
            [Atom("P", [Constant(name)]), Atom("P", [SortedConstant(name, "S")])])
        assert plain.args[0] == Constant(token)
        assert sorted_.args[0] == SortedConstant(token, "S")
        assert mapping.get_constant(name) == token


def test_a_problem_without_a_sorted_constant_is_written_as_before():
    # The unsorted problem has no membership line; with a sorted quantifier but no sorted
    # constant there is a non-emptiness line and no membership line.
    assumptions, goals, _ = _written([Atom("P", [Constant("a")])], Atom("Q", [Constant("b")]))
    assert assumptions == ["P(a)."] and goals == ["Q(b)."]
    assumptions, goals, _ = _written([SortedQuantifier("∀", x, "S", Atom("P", [x]))], Atom("Q", [Constant("b")]))
    assert assumptions == ["(all X (S(X) -> P(X))).", "(exists X0 S(X0))."]


def test_the_membership_atoms_are_assumptions_never_part_of_the_goal():
    # ⊢ Q(c:S ∧ c:T): the goal is the conjunction as written; the facts S(c), T(c) are in
    # the assumptions, not conjoined onto the goal (a goal `S(c) ∧ ...` could not be
    # proved even for a tautology).
    conclusion = And(Atom("Q", [SortedConstant("c", "S")]), Atom("Q", [SortedConstant("c", "T")]))
    assumptions, goals, _ = _written([], conclusion)
    assert goals == ["(Q(c) & Q(c))."]
    assert "S(c)." in assumptions and "T(c)." in assumptions


# --------------------------------------------------------------------------- #
# The real binary decides the fourteen problems of the sorted-constant matrix.
# --------------------------------------------------------------------------- #

_BINARY = Prover9Backend._binary()
live = pytest.mark.skipif(
    not _BINARY,
    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or "
           "put 'prover9' on PATH; the text-level tests above carry the claim")

# name, premises, conclusion (None: do the premises have no model?), verdict derived by hand
# from the definition in the module docstring, and the reason.
_PROBLEMS = [
    ("P1", ["∀x:Human Mortal(x)"], "Mortal(socrates:Human)", "valid",
     "socrates denotes an element of Human, and every Human is Mortal"),
    ("P2", ["∀x:Foo R(x)", "Q(g(alpha))"], "R(g(alpha))", "invalid",
     "U={0,1}, Foo={0}, R={0}, alpha=0, g(0)=1, Q={1}: the premises hold, R(g(alpha)) does not"),
    ("P3", ["∀x:Foo R(x)", "¬R(kay:Foo)"], None, "unsat",
     "kay is in Foo, so R(kay): a contradiction"),
    ("P4", ["∀x:Human Mortal(x)"], "Mortal(socrates)", "invalid",
     "U={0,1}, Human={0}, Mortal={0}, socrates=1"),
    ("P5", ["∀x ∀y x = y"], "∀x:A ∀z:A x = z", "valid",
     "the universe has one element, and A is a subset of it"),
    ("P6", ["∀x ∀y x = y", "∃x:A ∃z:A ¬(x = z)"], None, "unsat",
     "A would need two elements of a one-element universe"),
    ("P7", ["P(carl:A)", "Q(carl:B)"], "∃x:A Q(x)", "valid",
     "carl is in A and Q(carl)"),
    ("P8", ["P(carl)", "Q(carl:A)"], "∃x:A P(x)", "valid",
     "it is one constant; the sorted occurrence puts it in A"),
    ("P9", ["Mortal(socrates)"], "∃x:Human Mortal(x)", "invalid",
     "U={0,1}, Human={1}, Mortal={0}, socrates=0"),
    ("P10", ["∀x:Human ¬Evil(x)"], "¬Evil(socrates:Human)", "valid",
     "socrates is a Human, and no Human is Evil"),
    ("P11", [], "Mortal(socrates:Human)", "invalid",
     "U={0}, Human={0}, Mortal={}, socrates=0"),
    ("P12", [], "∃x:Human x = socrates:Human", "valid",
     "socrates is in Human and equals itself"),
    ("P13", [], "anna:S = bert:S", "invalid",
     "U={0,1}, S={0,1}, anna=0, bert=1"),
    ("P14", ["∀x:Human Mortal(x)", "∃x:Human Greek(x)"], "∃x:Human (Greek(x) ∧ Mortal(x))", "valid",
     "the Greek Human is Mortal"),
]


def _parse(text):
    return api.parse_any(text).formula


def _decide(goal, premises):
    return get_backend("prover9").decide(goal, premises, timeout=30000)


@live
def test_live_a_digit_leading_constant_is_one_symbol_whether_it_is_sorted_or_not():
    # Mortal(2008wins) ⊢ Mortal(2008wins:Human). Hand-derived: ONE constant, so the premise
    # is the conclusion. The writer spells it s2008wins; the sorted occurrence used to keep
    # the raw name, which Prover9 reads as another constant, and nothing was proved.
    premise = Atom("Mortal", [Constant("2008wins")])
    conclusion = Atom("Mortal", [SortedConstant("2008wins", "Human")])
    assert _decide(conclusion, [premise]).status == "proved"


@live
def test_live_two_constants_that_transliterate_alike_are_not_taken_for_one():
    # P(theta) ⊢ P(θ:Human) is NOT valid: two constants, theta and θ. U={0,1}, theta=0, θ=1,
    # Human={1}, P={0}: the premise holds, the conclusion does not. Both names are written
    # `theta` unless the sorted one is renamed like a plain constant (θ -> theta2), and Prover9
    # then PROVED this non-theorem.
    premise = Atom("P", [Constant("theta")])
    conclusion = Atom("P", [SortedConstant("θ", "Human")])
    result = _decide(conclusion, [premise])
    assert (result.status, result.reason) == ("unknown", "incomplete")
    # The control: one constant written two ways IS valid.
    assert _decide(Atom("P", [SortedConstant("theta", "Human")]), [premise]).status == "proved"


@live
def test_live_a_constant_named_like_a_sort_does_not_become_the_sort():
    # ∀x:human P(x, Human) ⊢ ∃x:human P(x, Human), where `Human` is a constant and `human` a
    # sort. Hand-derived: valid (the non-empty sort `human` has a witness for the universal).
    # The constant used to be spelled `human`, the sort's own name: Prover9 refuses a file in
    # which one spelling is both a predicate and a constant, and the verdict was an error.
    premise = SortedQuantifier("∀", x, "human", Atom("P", [x, Constant("Human")]))
    conclusion = SortedQuantifier("∃", x, "human", Atom("P", [x, Constant("Human")]))
    assert _decide(conclusion, [premise]).status == "proved"


@live
@pytest.mark.parametrize("name, premises, conclusion, verdict, reason", _PROBLEMS,
                         ids=[p[0] for p in _PROBLEMS])
def test_live_prover9_proves_exactly_what_the_definition_makes_valid(name, premises, conclusion,
                                                                     verdict, reason):
    goal = _parse("Contra ∧ ¬Contra") if conclusion is None else _parse(conclusion)
    result = get_backend("prover9").decide(goal, [_parse(p) for p in premises], timeout=30000)
    if verdict in ("valid", "unsat"):
        assert result.status == "proved", (name, reason, result)
    else:
        # Prover9's exit does not certify invalidity: "no proof" is UNKNOWN / incomplete.
        # What matters is that the invalid ones are NOT proved, and not an error.
        assert result.status == "unknown" and result.reason == "incomplete", (name, reason, result)
