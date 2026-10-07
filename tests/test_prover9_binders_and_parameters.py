r"""What the Prover9 problem writer owes the text it writes: names no one else has, no binder inside
the scope of one of its own name, a free variable read as the one unknown element it is, and no
silent change of the logic.

**Fresh names.** Prover9 writes a variable as the upper case of its name, so ``X0`` and ``x0`` are one
variable there. The witnesses of a counting quantifier are fresh against every name of the whole
problem, of every kind, compared case-folded; a variable ``X0`` is a name a witness ``x0`` must not take.

**No re-bound binder.** LADR renames a variable that a quantifier binds inside the scope of a quantifier
of the same name, to a symbol it picks itself (``x0``, ``x1``, ...), and picks it without looking at
the constants of the formula. Measured on Prover9 2026-8A: ``(all W (all W P(W, x0)))`` is clausified
to ``P(A, A)``, so the premise ``∀w ∀w P(w, x0)`` (which says ``∀e P(e, x0)``) proves ``P(alpha, alpha)``
when ``x0`` is a constant. The writer renames such a binder itself, and keeps every constant and
proposition off the spellings LADR picks. LADR's Skolem names (``c1``, ``f1``) skip every symbol of
the file, which was measured too, so a user symbol of that spelling is left alone.

**A free variable is a parameter.** ``Γ ⊨ φ`` iff every structure AND assignment that satisfies ``Γ``
satisfies ``φ``: one unknown element, the same in every premise and in the conclusion. Prover9 closes
each formula universally on its own, which is another question, so the writer replaces a free
variable by a fresh constant, problem-wide, and records it. The six problems of the decision, by hand:

* ``P(x) ⊢ P(alpha)`` is NOT valid: universe {0, 1}, x = 1, alpha = 0, P = {1};
* ``P(x) ⊢ P(x)`` is valid; ``P(x) ⊢ ∃y P(y)`` is valid; ``∀y P(y) ⊢ P(x)`` is valid;
* ``⊢ P(x) → P(alpha)`` is NOT valid: the same structure;
* ``P(x), Q(y) ⊢ ∀z (P(z) ∧ Q(z))`` is NOT valid: universe {0, 1}, x = 0, y = 1, P = {0}, Q = {1}.

**Łukasiewicz connectives** have no classical reading (``p ∨ ¬p`` is the maximum of ``p`` and ``1 − p``,
``1/2`` at ``p = 1/2``): the writer refuses them by name, as the single renderers do.

The live tests run the real Prover9 where there is one and skip, with a reason, where there is none.
"""

import re

import pytest

from unicode_logic_kit.atp.prover9_entailment import generate_prover9_input_with_mapping
from unicode_logic_kit.atp.protocol import Prover9Backend, get_backend
from unicode_logic_kit.fol._msfl_nodes import (
    LukEquivalence, LukImplication, LukNegation, SortedConstant, SortedCount, SortedQuantifier,
    StrongConjunction, StrongDisjunction, WeakConjunction, WeakDisjunction, free_variables, to_fol,
)
from unicode_logic_kit.fol._team_nodes import SlashedExists
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Implies, Not, Number, Quantifier, Variable,
)
from unicode_logic_kit.fol.prover9_input import parse_prover9

x, y, z, w = Variable("x"), Variable("y"), Variable("z"), Variable("w")
alpha = Constant("alpha")
G = Atom("G", [])


def P(*args):
    return Atom("P", list(args))


def FA(variable, body):
    return Quantifier("∀", variable, body)


def EX(variable, body):
    return Quantifier("∃", variable, body)


def _lines(text):
    lines = [line.strip() for line in text.splitlines()]
    assumptions = lines[lines.index("formulas(assumptions).") + 1:]
    assumptions = assumptions[:assumptions.index("end_of_list.")]
    goals = lines[lines.index("formulas(goals).") + 1:]
    goals = goals[:goals.index("end_of_list.")]
    return assumptions, goals


def _written(premises, conclusion):
    text, names = generate_prover9_input_with_mapping(premises, conclusion)
    return (*_lines(text), names)


def _binders(node, found=None):
    """The names a formula binds, outermost first, read as a flat list."""
    found = [] if found is None else found
    if isinstance(node, Quantifier):
        found.append(node.variable.name)
    for child in node._child_nodes():
        _binders(child, found)
    return found


def _rebinds(node, enclosing=frozenset()):
    """The variable names a formula binds INSIDE the scope of a binder of the same name."""
    found = []
    if isinstance(node, Quantifier):
        if node.variable.name in enclosing:
            found.append(node.variable.name)
        enclosing = enclosing | {node.variable.name}
    for child in node._child_nodes():
        found += _rebinds(child, enclosing)
    return found


_LADR_MINTED = re.compile(r"[xy](?:0|[1-9][0-9]*)")


# --------------------------------------------------------------------------- #
# Counting witnesses are fresh against every name of the problem, case-folded.
# --------------------------------------------------------------------------- #

def test_a_counting_witness_is_not_the_variable_that_differs_from_it_only_in_case():
    # ∀X0 ∃≥2 x R(x, X0), the variable written in upper case. Prover9 writes both X0 and x0 as X0, so a
    # witness x0 would bind the user's X0 again: ∃a≠b R(a, a) ∧ R(b, a), which R(aa,aa), R(bb,aa) give.
    conclusion = FA(Variable("X0"), Count("ge", Number(2), x, Atom("R", [x, Variable("X0")])))
    _, goals, _ = _written([], conclusion)
    goal = parse_prover9(goals[0])
    names = _binders(goal)
    assert len(names) == 3 and names[0] == "x0"
    assert len(set(names)) == 3, f"a witness has the name of a binder around it: {goals[0]}"
    assert _rebinds(goal) == []


def test_the_sorted_counting_quantifier_gets_the_same_witnesses():
    # The sorted variant of the same problem: ∀X1:S ∃≥2 x:S R(x, X1).
    conclusion = SortedQuantifier("∀", Variable("X1"), "S",
                                  SortedCount("ge", Number(2), x, "S", Atom("R", [x, Variable("X1")])))
    assumptions, goals, _ = _written([], conclusion)
    goal = parse_prover9(goals[0])
    assert len(set(_binders(goal))) == len(_binders(goal)), goals[0]
    assert _rebinds(goal) == []


@pytest.mark.parametrize("taken", [
    pytest.param(Atom("x0", [alpha]), id="a predicate x0"),
    pytest.param(Atom("Q", [Function("x0", [alpha])]), id="a function x0"),
    pytest.param(Atom("Q", [Constant("x0")]), id="a constant x0"),
    pytest.param(Atom("X0", [alpha]), id="a predicate X0"),
    pytest.param(Atom("Q", [SortedConstant("a", "x0")]), id="a sort x0"),
])
def test_a_witness_has_no_name_of_the_problem_in_any_kind(taken):
    # The witnesses of ∃≥2 x P(x) are called x0 and x1 when nothing in the problem is: the avoid set
    # holds the names of EVERY kind (a predicate, a function, a constant, a sort), case-folded.
    conclusion = Count("ge", Number(2), x, Atom("P", [x]))
    _, goals, _ = _written([taken], conclusion)
    witnesses = _binders(parse_prover9(goals[0]))
    assert len(witnesses) == 2 and len(set(witnesses)) == 2 and "x0" not in witnesses


def test_the_witnesses_avoid_the_names_of_the_other_formulas_and_of_the_sort_facts():
    premises = [Quantifier("∃", Variable("X1"), Atom("Q", [Variable("X1")])), Atom("R", [Constant("y0")])]
    conclusion = SortedCount("ge", Number(2), y, "Y", Atom("P", [y]))
    _, goals, _ = _written(premises, conclusion)
    witnesses = _binders(parse_prover9(goals[0]))
    assert "y0" not in witnesses and len(set(witnesses)) == len(witnesses)


# --------------------------------------------------------------------------- #
# No binder inside the scope of a binder of its own name.
# --------------------------------------------------------------------------- #

def test_a_re_bound_binder_is_renamed_and_means_what_it_meant():
    # ∀w ∀w P(w, x0) says ∀e P(e, x0): the occurrence of w belongs to the INNER binder.
    premise = FA(w, FA(w, P(w, Constant("x0"))))
    assumptions, goals, names = _written([premise], P(alpha, alpha))
    read = parse_prover9(assumptions[0])
    assert _rebinds(read) == []
    outer, inner = read, read.formula
    assert isinstance(outer, Quantifier) and isinstance(inner, Quantifier)
    atom = inner.formula
    assert atom.args[0] == inner.variable and inner.variable != outer.variable
    assert atom.args[1] == Constant(names.symbols[("function", "x0", 0)])


def test_an_existential_inside_a_universal_of_one_name_is_renamed_too():
    premise = FA(w, EX(w, P(w, Constant("x0"))))
    assumptions, _, _ = _written([premise], EX(y, P(y, y)))
    read = parse_prover9(assumptions[0])
    assert _rebinds(read) == []
    assert read.type == "∀" and read.formula.type == "∃"
    assert read.formula.formula.args[0] == read.formula.variable


def test_the_inner_binder_keeps_its_name_for_the_occurrences_that_are_its_own_and_not_the_outer_ones():
    # ∀w (P(w) ∧ ∀w Q(w) ∧ R(w)): the first and the last w are the outer binder's, the middle one the inner's.
    premise = FA(w, And(And(P(w), FA(w, Atom("Q", [w]))), Atom("R", [w])))
    assumptions, _, _ = _written([premise], G)
    read = parse_prover9(assumptions[0])
    assert _rebinds(read) == []
    outer = read
    conj = outer.formula
    left, last = conj.left, conj.right
    first, inner = left.left, left.right
    assert first.args[0] == outer.variable and last.args[0] == outer.variable
    assert inner.formula.args[0] == inner.variable != outer.variable


def test_a_formula_without_a_re_bound_binder_is_written_as_it_always_was():
    # Two sibling quantifiers of one name are not re-bound: LADR keeps them (measured) and so does the writer.
    premise = And(FA(w, Atom("R", [w])), FA(w, P(w, Constant("a"))))
    assumptions, _, _ = _written([premise], alpha)
    assert assumptions == ["((all W R(W)) & (all W P(W, a)))."]


def test_the_binders_of_the_counting_expansion_are_not_re_bound_either():
    # ∃≥2 x ∃≥2 y R(x, y) written for a problem that also binds y0 and x1 around it.
    inner = Count("ge", Number(2), y, Atom("R", [x, y]))
    premise = FA(Variable("y0"), EX(Variable("x1"), Count("ge", Number(2), x, inner)))
    assumptions, _, _ = _written([premise], alpha)
    assert _rebinds(parse_prover9(assumptions[0])) == []


# --------------------------------------------------------------------------- #
# The spellings LADR picks for itself are no name of the user's.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", ["x0", "x1", "x17", "y0", "y3"])
def test_a_constant_spelled_like_a_variable_LADR_picks_is_written_under_another_word(name):
    premise = FA(w, FA(w, P(w, Constant(name))))
    assumptions, goals, names = _written([premise], P(Constant(name), alpha))
    token = names.symbols[("function", name, 0)]
    assert token != name and _LADR_MINTED.fullmatch(token) is None
    assert names.reverse()[token] == name
    # No constant of the text is spelled like a name LADR picks (the variables are upper case).
    text = " ".join(assumptions + goals)
    assert not re.search(r"\b[xy][0-9]+\b", text), text


@pytest.mark.parametrize("name", ["x0", "y12"])
def test_a_proposition_spelled_like_a_variable_LADR_picks_is_written_under_another_word(name):
    assumptions, goals, names = _written([Atom(name, [])], Atom(name, []))
    token = names.symbols[("predicate", name, 0)]
    assert token != name and _LADR_MINTED.fullmatch(token) is None
    assert assumptions == goals == [f"{token}."]


def test_a_symbol_with_arguments_keeps_a_spelling_that_no_variable_LADR_picks_has():
    # x0(a) is the symbol x0/1, and the variables LADR picks are symbols of no arguments: no capture.
    assumptions, _, names = _written([Atom("x0", [alpha]), Atom("Q", [Function("y1", [alpha])])], G)
    assert names.symbols[("predicate", "x0", 1)] == "x0"
    assert names.symbols[("function", "y1", 1)] == "y1"


def test_the_names_of_the_Skolem_symbols_of_LADR_are_left_alone():
    # LADR's c1, c2, ... and f1, f2, ... skip every symbol of the file (measured), so a constant c1
    # and a function f1 of the problem keep their spelling.
    _, _, names = _written([Atom("Q", [Constant("c1"), Function("f1", [Constant("c2")])])], G)
    assert names.symbols[("function", "c1", 0)] == "c1"
    assert names.symbols[("function", "f1", 1)] == "f1"
    assert names.symbols[("function", "c2", 0)] == "c2"


def test_a_second_symbol_of_the_name_x_or_y_does_not_take_a_name_LADR_picks():
    # A proposition x next to the constant x: the second one cannot be x2 (a name LADR picks).
    _, _, names = _written([Atom("x", []), Atom("Q", [Constant("x")])], G)
    tokens = [token for (kind, name, arity), token in names.symbols.items() if name == "x"]
    assert len(set(tokens)) == 2 and all(_LADR_MINTED.fullmatch(t) is None for t in tokens)


def test_the_tokens_of_the_symbols_of_a_problem_stay_pairwise_distinct():
    atoms = [Atom("P", [Constant("x0"), Constant("x0_"), Constant("X0"), Constant("x00")]),
             Atom("x0", []), Atom("x0_", []), Atom("Q", [Function("x0", [alpha])])]
    _, _, names = _written(atoms, G)
    assert len(set(names.symbols.values())) == len(names.symbols)


# --------------------------------------------------------------------------- #
# A free variable is a parameter: a constant of the problem.
# --------------------------------------------------------------------------- #

def _closed(text_line):
    return free_variables(parse_prover9(text_line)) == set()


def test_a_free_variable_is_written_as_a_constant_and_the_text_is_closed():
    assumptions, goals, names = _written([P(x)], P(alpha))
    assert assumptions == ["P(x)."] and goals == ["P(alpha)."]
    assert names.free_variables == {"x": "x"}
    assert all(_closed(line) for line in assumptions + goals)


def test_a_free_variable_is_one_constant_in_every_formula_of_the_problem():
    assumptions, goals, names = _written([P(x), Atom("Q", [x, y])], P(x))
    token = names.free_variables["x"]
    assert assumptions[0] == f"P({token})." and goals == [f"P({token})."]
    assert names.free_variables["y"] != token
    assert assumptions[1] == f"Q({token}, {names.free_variables['y']})."


def test_a_bound_occurrence_of_the_name_of_a_free_variable_is_untouched():
    # P(x) ∧ ∀x Q(x): the first x is free, the second is bound.
    premise = And(P(x), FA(x, Atom("Q", [x])))
    assumptions, _, names = _written([premise], G)
    read = parse_prover9(assumptions[0])
    assert read.left.args[0] == Constant(names.free_variables["x"])
    assert read.right.variable == Variable("x") and read.right.formula.args[0] == Variable("x")


def test_a_free_variable_gets_a_constant_that_is_no_symbol_of_the_problem():
    # A constant x is already there: the constant of the free variable x is another one.
    assumptions, _, names = _written([P(x), Atom("Q", [Constant("x")])], G)
    assert names.free_variables["x"] != names.symbols[("function", "x", 0)]
    assert assumptions == [f"P({names.free_variables['x']}).", "Q(x)."]
    assert names.reverse()[names.free_variables["x"]] == "x"


@pytest.mark.parametrize("name", ["X", "x0", "W"])
def test_a_free_variable_called_like_a_variable_Prover9_reads_or_a_name_LADR_picks(name):
    # The constant must be one Prover9 reads as a constant: not an upper-case word, not x<k>.
    assumptions, _, names = _written([P(Variable(name))], P(alpha))
    token = names.free_variables[name]
    assert token[0].islower() and _LADR_MINTED.fullmatch(token) is None
    assert assumptions == [f"P({token})."]


def test_two_free_variables_that_differ_only_in_case_are_two_constants():
    # x in one formula and X in another are two variables of the kit (no route reads them as one).
    _, _, names = _written([P(x)], P(Variable("X")))
    assert names.free_variables["x"] != names.free_variables["X"]


def test_a_free_variable_in_a_counting_quantifier_and_a_sorted_one():
    premise = Count("ge", Number(2), y, Atom("R", [y, x]))
    conclusion = SortedQuantifier("∃", y, "S", Atom("R", [y, x]))
    assumptions, goals, names = _written([premise], conclusion)
    token = names.free_variables["x"]
    assert all(_closed(line) for line in assumptions + goals)
    assert all(token in line for line in (assumptions[0], goals[0]))


def test_a_slashed_quantifier_with_a_free_slash_name_is_refused_and_not_written_as_a_plain_quantifier():
    # ∃y/{z} R(y, z) has team semantics and no classical export. Its slash set names the free variable z;
    # replacing z by a constant would empty the set and leave the plain ∃y R(y, c): a classical formula
    # for a construct that is not one.
    formula = SlashedExists(y, ("z",), Atom("R", [y, z]))
    for premises, conclusion in (([formula], G), ([], formula)):
        with pytest.raises(NotImplementedError) as refused:
            generate_prover9_input_with_mapping(premises, conclusion)
        assert "team semantics" in str(refused.value)


# --------------------------------------------------------------------------- #
# Łukasiewicz connectives are refused by name.
# --------------------------------------------------------------------------- #

p, q = Atom("p", []), Atom("q", [])
_LUKASIEWICZ = [WeakConjunction(p, q), WeakDisjunction(p, LukNegation(p)), StrongConjunction(p, q),
                StrongDisjunction(p, q), LukNegation(p), LukImplication(p, q), LukEquivalence(p, q)]


@pytest.mark.parametrize("node", _LUKASIEWICZ, ids=[type(n).__name__ for n in _LUKASIEWICZ])
def test_the_writer_refuses_a_lukasiewicz_connective_by_name(node):
    for premises, conclusion in (([], node), ([node], p), ([], Not(node)), ([], FA(x, Implies(P(x), node)))):
        with pytest.raises(NotImplementedError) as refused:
            generate_prover9_input_with_mapping(premises, conclusion)
        message = str(refused.value)
        assert type(node).__name__ in message and "WRONG logic" in message


def test_the_backend_reports_a_lukasiewicz_connective_as_unsupported_and_never_as_proved():
    verdict = get_backend("prover9").decide(WeakDisjunction(p, LukNegation(p)), [],
                                            prover9_path="no-such-prover9", use_wsl=False)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert "WeakDisjunction" in verdict.detail


def test_the_explicit_classical_collapse_is_still_a_formula_the_writer_writes():
    # to_fol collapses the connective on request: p ∨ ¬p is then the classical excluded middle.
    _, goals, _ = _written([], to_fol(WeakDisjunction(p, LukNegation(p))))
    assert goals == ["(p | -(p))."]


# --------------------------------------------------------------------------- #
# Against the real Prover9.
# --------------------------------------------------------------------------- #

_BINARY = Prover9Backend._binary()
live = pytest.mark.skipif(
    _BINARY is None,
    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or "
           "put 'prover9' on PATH; the text-level tests above carry the claim")


def _decide(goal, premises):
    return get_backend("prover9").decide(goal, premises, timeout=30000)


def _a(*names):
    return [Constant(n) for n in names]


# premises, goal, "valid" | "invalid", why (by hand)
_x0, _X0 = Constant("x0"), Constant("X0")
_PROBLEMS = [
    ("rebound universal, x0",
     [FA(w, FA(w, P(w, _x0)))], P(alpha, alpha), "invalid",
     "U={0,1}, x0=0, alpha=1, P={(0,0),(1,0)}: the premise says P(e, 0) for every e; P(1,1) is false"),
    ("rebound universal, constant X0 (written x0 by the old writer)",
     [FA(w, FA(w, P(w, _X0)))], P(alpha, alpha), "invalid", "the same structure with X0 = 0"),
    ("rebound three deep, x1",
     [FA(w, FA(w, FA(w, P(w, Constant("x1")))))], P(alpha, alpha), "invalid", "the same structure with x1 = 0"),
    ("rebound universal, y0",
     [FA(w, FA(w, P(w, Constant("y0"))))], P(alpha, alpha), "invalid", "the same structure with y0 = 0"),
    ("universal over existential, x0",
     [FA(w, EX(w, P(w, _x0)))], EX(y, P(y, y)), "invalid",
     "U={0,1}, x0=0, P={(1,0)}: some element is P-related to x0; nothing is P-related to itself"),
    ("existential over existential, x0",
     [EX(w, EX(w, P(w, _x0)))], EX(y, P(y, y)), "invalid", "the same structure"),
    ("rebound universal, the instance",
     [FA(w, FA(w, P(w, _x0)))], P(alpha, _x0), "valid", "take e = alpha"),
    ("universal over existential, the weaker claim",
     [FA(w, EX(w, P(w, _x0)))], EX(y, P(y, _x0)), "valid", "the premise is ∃w P(w, x0)"),
    ("a constant c1 and the Skolem constant of LADR",
     [EX(w, Atom("Q", [w]))], Atom("Q", [Constant("c1")]), "invalid",
     "U={0,1}, Q={0}, c1=1"),
    ("a function f1 and the Skolem function of LADR",
     [FA(x, EX(y, P(x, y)))], P(alpha, Function("f1", [alpha])), "invalid",
     "U={0,1}, P={(0,1),(1,0)}, alpha=0, f1(0)=0: P(0, f1(0)) = P(0, 0) is false"),
    ("counting witness against X0: not valid",
     [P(Constant("aa"), Constant("aa")), P(Constant("bb"), Constant("aa")),
      Not(Atom("=", [Constant("aa"), Constant("bb")]))],
     FA(Variable("X0"), Count("ge", Number(2), x, P(x, Variable("X0")))), "invalid",
     "U={0,1}, aa=0, bb=1, P={(0,0),(1,0)}: nothing is P-related to element 1"),
    ("counting witness against X0, the valid instance",
     [P(Constant("aa"), Constant("aa")), P(Constant("bb"), Constant("aa")),
      Not(Atom("=", [Constant("aa"), Constant("bb")]))],
     Count("ge", Number(2), x, P(x, Constant("aa"))), "valid", "aa and bb"),
    ("sorted counting witness against X1: not valid",
     [P(SortedConstant("aa", "S"), SortedConstant("aa", "S")), P(SortedConstant("bb", "S"), SortedConstant("aa", "S")),
      Not(Atom("=", [SortedConstant("aa", "S"), SortedConstant("bb", "S")]))],
     SortedQuantifier("∀", Variable("X1"), "S",
                      SortedCount("ge", Number(2), x, "S", P(x, Variable("X1")))), "invalid",
     "U={0,1}, S=U, aa=0, bb=1, P={(0,0),(1,0)}"),
    # the decision on a free variable
    ("P(x) |- P(alpha)", [P(x)], P(alpha), "invalid", "U={0,1}, x=1, alpha=0, P={1}"),
    ("P(x) |- P(x)", [P(x)], P(x), "valid", "the premise"),
    ("P(x) |- ∃y P(y)", [P(x)], EX(y, P(y)), "valid", "witness x"),
    ("∀y P(y) |- P(x)", [FA(y, P(y))], P(x), "valid", "instance x"),
    ("|- P(x) -> P(alpha)", [], Implies(P(x), P(alpha)), "invalid", "U={0,1}, x=1, alpha=0, P={1}"),
    ("P(x), Q(y) |- ∀z (P(z) ∧ Q(z))", [P(x), Atom("Q", [y])], FA(z, And(P(z), Atom("Q", [z]))), "invalid",
     "U={0,1}, x=0, y=1, P={0}, Q={1}"),
    ("a free variable and a constant of its name", [P(x), Atom("Q", [Constant("x")])], P(Constant("x")), "invalid",
     "U={0,1}, x=1, the constant x=0, P={1}"),
    ("a free variable that is also bound", [And(P(x), FA(x, Atom("Q", [x])))], FA(y, Atom("Q", [y])), "valid",
     "the second conjunct says that Q holds of everything"),
]


@live
@pytest.mark.parametrize("name, premises, goal, verdict, reason", _PROBLEMS, ids=[p[0] for p in _PROBLEMS])
def test_live_prover9_answers_as_the_definition_says(name, premises, goal, verdict, reason):
    result = _decide(goal, premises)
    if verdict == "valid":
        assert result.status == "proved", (name, reason, result)
    else:
        # Prover9's exit does not certify invalidity: "no proof" is UNKNOWN / incomplete. What matters
        # is that an invalid problem is NOT proved and none is an input error.
        assert (result.status, result.reason) == ("unknown", "incomplete"), (name, reason, result)
