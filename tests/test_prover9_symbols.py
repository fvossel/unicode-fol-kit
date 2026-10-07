r"""One name, several symbols: the Prover9 problem writer keys a symbol on (kind, name, arity).

Prover9 keeps ONE symbol per spelling. It refuses a file that uses a spelling at two
arities (``The following symbols are used with multiple arities: P/2, P/1``) and one that
uses it both as a relation and as a function (``...used as both relation and function
symbols: p/0``); measured on Prover9 2026-8A. The kit does not: ``P(x)`` and ``P(x, y)``
are two predicates, a proposition ``p``, a predicate ``p(x)``, the constant ``p`` and the
function ``p(x)`` are four more, and a SORT ``S`` is the unary predicate ``S`` (the sort
and the predicate of that name are ONE symbol: ``∀x:S φ`` is ``∀x (S(x) → φ)`` and a
plain atom ``S(c)`` says that ``c`` is in ``S``). The writer therefore gives the FIRST
symbol of a spelling that spelling and every later one with the same name a token that is
no other symbol's spelling (``P`` at two arities is ``P`` and ``P2``), and records each in
``Prover9NameMap.symbols``.

A sort goes through the same renaming as every other symbol: the writer lowers a sorted
node to the plain guard first, so a non-ASCII sort name is written under an ASCII
replacement, a sort named like a constant of the problem (``person`` and ``person``) gives
the constant another token, and a predicate ``S`` of another arity is another symbol.

The counting quantifier is written as that many distinct witnesses, whose names are minted.
Every name the writer mints is fresh against every variable name of the whole problem, so an
expansion never rebinds a variable of the formula around it.

What is pinned here:

* the exact text, derived by hand from those rules (the first symbol keeps its name, the
  later ones get the smallest numeric suffix that is no other symbol's name);
* that the map records every symbol, and that a lookup that was unambiguous still works;
* for random symbol sets: tokens are pairwise distinct, are words Prover9 reads, and a
  symbol that is the only one of its name keeps it;
* against the REAL Prover9, where there is one (the live tests skip, with a reason, where
  there is none): problems with one name at two arities, one name as a predicate and as a
  constant, non-ASCII and keyword-like sort names, and sorted and plain constants of one
  name. Each of the hand-derived problems is answered as the definition says; and a few
  hundred generated problems are answered as Z3 answers the same problem with every symbol
  given a name of its own by the test (Prover9 proves exactly what Z3 proves; no problem
  ends as a Prover9 input error). The control: the same problems written by joining the
  single-node renderers (no whole-problem view) are mostly refused or misread.
"""

import random
import re

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import prover9_entailment as p9
from unicode_logic_kit.atp.prover9_entailment import (
    Prover9Rejected, _sanitize_for_prover9, generate_prover9_input_with_mapping,
)
from unicode_logic_kit.atp.protocol import Prover9Backend, get_backend
from unicode_logic_kit.fol._msfl_nodes import SortedConstant, SortedQuantifier
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Iff, Implies, Not, Number, Or, Quantifier, Variable,
)

x, y = Variable("x"), Variable("y")


def N(name):
    """A proposition: an atom with no arguments."""
    return Atom(name, [])


def _lines(text):
    """The formula lines of the ``assumptions`` list and of the ``goals`` list of a written problem."""
    lines = [line.strip() for line in text.splitlines()]
    assumptions = lines[lines.index("formulas(assumptions).") + 1:]
    assumptions = assumptions[:assumptions.index("end_of_list.")]
    goals = lines[lines.index("formulas(goals).") + 1:]
    goals = goals[:goals.index("end_of_list.")]
    return assumptions, goals


def _written(premises, conclusion):
    text, names = generate_prover9_input_with_mapping(premises, conclusion)
    return (*_lines(text), names)


# --------------------------------------------------------------------------- #
# One name, several symbols: the exact text.
# --------------------------------------------------------------------------- #

def test_one_predicate_at_two_arities_is_two_symbols():
    # P(a) ⊢ P(a, b): P of one argument and P of two are two predicates. The first keeps
    # `P`; the second takes the smallest numeric suffix that is nobody's name: P2.
    assumptions, goals, names = _written([Atom("P", [Constant("a")])],
                                         Atom("P", [Constant("a"), Constant("b")]))
    assert assumptions == ["P(a)."] and goals == ["P2(a, b)."]
    assert names.symbols == {("predicate", "P", 1): "P", ("predicate", "P", 2): "P2",
                             ("function", "a", 0): "a", ("function", "b", 0): "b"}
    assert names.get_symbol("predicate", "P", 2) == "P2"
    assert names.reverse()["P2"] == "P" and names.reverse()["P"] == "P"


def test_the_first_symbol_in_the_problem_keeps_the_name():
    # The same two predicates, met in the other order: the premise now has the binary one.
    assumptions, goals, names = _written([Atom("P", [Constant("a"), Constant("b")])],
                                         Atom("P", [Constant("a")]))
    assert assumptions == ["P(a, b)."] and goals == ["P2(a)."]
    assert names.symbols[("predicate", "P", 2)] == "P" and names.symbols[("predicate", "P", 1)] == "P2"


def test_a_replacement_is_never_the_name_of_another_symbol():
    # P at arity 1, a user predicate that is really called P2, and P at arity 2: the
    # second P cannot be P2 (taken, by a symbol of the problem), so it is P3.
    assumptions, goals, _ = _written(
        [Atom("P", [Constant("a")]), Atom("P2", [Constant("a")])],
        Atom("P", [Constant("a"), Constant("b")]))
    assert assumptions == ["P(a).", "P2(a)."] and goals == ["P3(a, b)."]


def test_one_function_at_two_arities_is_two_symbols():
    assumptions, goals, names = _written(
        [Atom("P", [Function("f", [Constant("a")])])],
        Atom("P", [Function("f", [Constant("a"), Constant("b")])]))
    assert assumptions == ["P(f(a))."] and goals == ["P(f2(a, b))."]
    assert names.symbols[("function", "f", 2)] == "f2"


def test_a_predicate_and_a_function_of_one_name_are_two_symbols():
    # f(f(a)): the outer f is a predicate, the inner one a function.
    assumptions, goals, names = _written(
        [Atom("f", [Function("f", [Constant("a")])])], Atom("Goal", []))
    assert assumptions == ["f(f2(a))."]
    assert names.symbols[("predicate", "f", 1)] == "f" and names.symbols[("function", "f", 1)] == "f2"


def test_a_predicate_and_a_constant_of_one_name_are_two_symbols():
    # p(p): the predicate p and the constant p (lower case: no variable rename applies).
    assumptions, _, names = _written([Atom("p", [Constant("p")])], Atom("Goal", []))
    assert assumptions == ["p(p2)."]
    assert names.get_constant("p") == "p2"


def test_a_proposition_and_a_predicate_of_one_name_are_two_symbols():
    assumptions, goals, names = _written([N("p")], Atom("p", [Constant("a")]))
    assert assumptions == ["p."] and goals == ["p2(a)."]
    assert names.get_nullary("p") == "p" and names.get_symbol("predicate", "p", 1) == "p2"


def test_a_constant_and_a_function_of_one_name_are_two_symbols():
    assumptions, goals, _ = _written([Atom("P", [Constant("a")])],
                                     Atom("P", [Function("a", [Constant("b")])]))
    assert assumptions == ["P(a)."] and goals == ["P(a2(b))."]


def test_the_same_symbol_twice_is_one_symbol():
    # Nothing is renamed when a name has one symbol: P(a) twice is P(a) twice.
    assumptions, goals, names = _written([Atom("P", [Constant("a")]), Atom("P", [Constant("a")])],
                                         Atom("P", [Constant("a")]))
    assert assumptions == ["P(a).", "P(a)."] and goals == ["P(a)."]
    assert len(names.symbols) == 2


def test_a_name_with_one_symbol_is_looked_up_as_before():
    # `get`, `get_constant`, `get_nullary` and `mapping` keep answering for a name that
    # has one symbol; for a name with several, `mapping` and `get` answer for the first.
    _, _, names = _written(
        [Atom("P", [Constant("Gaseous")]), N("Rain"), Atom("Q", [Constant("a")])],
        Atom("P", [Constant("a"), Constant("b")]))
    assert names.get_constant("Gaseous") == "gaseous" and names.constants == {"Gaseous": "gaseous"}
    assert names.get_nullary("Rain") == "rain" and names.nullary_predicates == {"Rain": "rain"}
    assert names.get("Q") == "Q" and names.mapping["Q"] == "Q"
    assert names.get("P") == "P" and names.mapping["P"] == "P"          # the first of two
    assert names.symbols[("predicate", "P", 2)] == "P2"


def test_a_variable_shaped_constant_and_a_predicate_of_that_word_stay_two_symbols():
    # The OWL pun: class Person (a predicate) and individual Person (a constant). The constant
    # is read as a variable when written bare, so it is renamed; the predicate keeps the word.
    assumptions, _, names = _written([Atom("Person", [Constant("Person")])], Atom("Goal", []))
    assert assumptions == ["Person(person)."]
    assert names.constants == {"Person": "person"} and names.mapping["Person"] == "Person"


def test_the_writer_text_for_a_problem_without_a_clash_is_unchanged():
    assumptions, goals, names = _written(
        [Quantifier("∀", x, Atom("Human", [x])), Atom("Mortal", [Function("f", [Constant("a")])])],
        Atom("Mortal", [Constant("a")]))
    assert assumptions == ["(all X Human(X)).", "Mortal(f(a))."] and goals == ["Mortal(a)."]
    assert all(token == name for (_, name, _), token in names.symbols.items())


# --------------------------------------------------------------------------- #
# Sorts are symbols like the others.
# --------------------------------------------------------------------------- #

def test_a_sort_and_a_constant_of_one_name_are_two_symbols():
    # ∀x:person P(x) ⊢ P(person:person): the sort person (the unary predicate person), and the
    # CONSTANT person. The constant is the later symbol, so it is person2; the non-emptiness and
    # membership facts use the sort's own name.
    assumptions, goals, names = _written(
        [SortedQuantifier("∀", x, "person", Atom("P", [x]))],
        Atom("P", [SortedConstant("person", "person")]))
    assert assumptions == ["(all X (person(X) -> P(X))).", "(exists X0 person(X0)).",
                           "person(person2)."]
    assert goals == ["P(person2)."]
    assert names.get_constant("person") == "person2" and names.get_sort("person") == "person"


def test_a_sort_and_the_unary_predicate_of_its_name_are_one_symbol():
    # The sort S and a plain S(c): one symbol, one spelling, nothing renamed.
    assumptions, goals, names = _written(
        [SortedQuantifier("∀", x, "S", Atom("P", [x]))], Atom("S", [Constant("c")]))
    assert assumptions == ["(all X (S(X) -> P(X))).", "(exists X0 S(X0))."]
    assert goals == ["S(c)."]
    assert [key for key in names.symbols if key[1] == "S"] == [("predicate", "S", 1)]


def test_a_predicate_of_the_name_of_a_sort_and_another_arity_is_another_symbol():
    assumptions, goals, names = _written(
        [SortedQuantifier("∀", x, "S", Atom("P", [x]))],
        Atom("S", [Constant("a"), Constant("b")]))
    assert assumptions == ["(all X (S(X) -> P(X))).", "(exists X0 S(X0))."]
    assert goals == ["S2(a, b)."]
    assert names.get_sort("S") == "S" and names.get_symbol("predicate", "S", 2) == "S2"


def test_a_proposition_of_the_name_of_a_sort_is_another_symbol():
    # S as a proposition would be read as a variable (upper case, no argument): it is the
    # lower-case token s; the sort S keeps its name.
    assumptions, _, names = _written(
        [SortedQuantifier("∀", x, "S", Atom("P", [x])), N("S")], Atom("Goal", []))
    assert assumptions == ["(all X (S(X) -> P(X))).", "s.", "(exists X0 S(X0))."]
    assert names.get_nullary("S") == "s"


def test_a_non_ascii_sort_name_is_written_under_an_ascii_replacement():
    # The sort Größe: ö and ß are written as the escapes u00f6 and u00df, the first letter
    # is lower-cased like every synthesised token. The membership fact uses the same token.
    assumptions, goals, names = _written(
        [SortedQuantifier("∀", x, "Größe", Atom("P", [x]))],
        Atom("P", [SortedConstant("a", "Größe")]))
    token = "gru00f6u00dfe"
    assert assumptions == [f"(all X ({token}(X) -> P(X))).", f"(exists X0 {token}(X0)).", f"{token}(a)."]
    assert goals == ["P(a)."]
    assert names.get_sort("Größe") == token and names.reverse()[token] == "Größe"


def test_a_digit_leading_sort_name_is_written_under_a_word_that_starts_with_a_letter():
    assumptions, _, _ = _written([SortedQuantifier("∀", x, "2nd", Atom("P", [x]))], Atom("Goal", []))
    assert assumptions == ["(all X (s2nd(X) -> P(X))).", "(exists X0 s2nd(X0))."]


@pytest.mark.parametrize("sort, token", [("all", "all2"), ("exists", "exists2"), ("v", "v")])
def test_a_sort_named_like_a_keyword_is_written_under_a_name_that_is_not_one(sort, token):
    # LADR reads `exists(X) & ...` as the quantifier `exists X` and a stray `&`, and `all(X)` the
    # same way (measured on Prover9 2026-8A; the live tests below decide the problems). So the two
    # quantifier words are renamed like a spelling that is taken (all2, exists2). `v`, the infix
    # operator of Prover9's table, is read as an ordinary symbol everywhere: it stays.
    assumptions, goals, names = _written([SortedQuantifier("∀", x, sort, Atom("P", [x]))],
                                         Atom("P", [SortedConstant("a", sort)]))
    assert assumptions == [f"(all X ({token}(X) -> P(X))).", f"(exists X0 {token}(X0)).", f"{token}(a)."]
    assert goals == ["P(a)."]
    assert names.get_sort(sort) == token and names.reverse()[token] == sort


@pytest.mark.parametrize("word", ["all", "exists"])
def test_a_predicate_a_function_and_a_constant_named_like_a_quantifier_are_renamed_too(word):
    assumptions, goals, names = _written(
        [Atom(word, [Constant("a")]), Atom("P", [Function(word, [Constant("a")])])],
        Atom("P", [Constant(word)]))
    # The word is no legal symbol at all, so even the first symbol of the name is renamed: the
    # predicate, the function and the constant are word2, word3 and word4.
    assert assumptions == [f"{word}2(a).", f"P({word}3(a))."] and goals == [f"P({word}4)."]
    assert names.get_symbol("predicate", word, 1) == f"{word}2"
    assert names.get_symbol("function", word, 1) == f"{word}3" and names.get_constant(word) == f"{word}4"


def test_a_sort_that_is_a_dollar_word_is_refused_by_name():
    with pytest.raises(NotImplementedError, match=r"the sort '\$i' is a '\$'-word"):
        generate_prover9_input_with_mapping([SortedQuantifier("∀", x, "$i", Atom("P", [x]))],
                                            Atom("Goal", []))


def test_a_constant_spelled_like_a_sort_is_another_symbol_than_the_sort():
    # carl:A and a plain carl are ONE constant; the constant `A` and the sort A are two
    # symbols. The constant is variable-shaped (renamed `a`); the sort A keeps `A`.
    assumptions, goals, names = _written(
        [Atom("P", [Constant("A")]), Atom("Q", [SortedConstant("carl", "A")])],
        Atom("Q", [Constant("carl")]))
    assert assumptions == ["P(a).", "Q(carl).", "(exists X0 A(X0)).", "A(carl)."]
    assert goals == ["Q(carl)."]
    assert names.get_constant("A") == "a" and names.get_sort("A") == "A"


# --------------------------------------------------------------------------- #
# The counting witnesses are fresh against the whole problem.
# --------------------------------------------------------------------------- #

def _rebinds(line, enclosing=frozenset()):
    """The variable names a written formula binds INSIDE the scope of a binder of the same name
    (``(all X0 ... (exists X0 ...))``), read back with the kit's own Prover9 reader."""
    from unicode_logic_kit.fol.prover9_input import parse_prover9

    def walk(node, bound):
        found = []
        if isinstance(node, Quantifier):
            if node.variable.name in bound:
                found.append(node.variable.name)
            bound = bound | {node.variable.name}
        for child in node._child_nodes():
            found += walk(child, bound)
        return found

    return walk(parse_prover9(line), frozenset(enclosing))


def test_a_counting_witness_does_not_rebind_a_variable_of_the_formula_around_it():
    # ∀x0 (R(x0) → ∃≥2 x S(x)). The Count does not mention x0, so its own witnesses (named
    # like the counting variable x: x0, x1) used to include x0 and rebind the enclosing binder:
    # (all X0 (R(X0) -> (exists X0 (exists X1 ...)))). The witnesses now avoid x0 and x as well.
    x0 = Variable("x0")
    formula = Quantifier("∀", x0, Implies(Atom("R", [x0]), Count("ge", Number(2), x, Atom("S", [x]))))
    assumptions, _, _ = _written([formula], Atom("Goal", []))
    assert assumptions == [
        "(all X0 (R(X0) -> (exists X1 (exists X2 ((S(X1) & S(X2)) & (X1 != X2))))))."]
    assert _rebinds(assumptions[0]) == []


def test_a_counting_witness_avoids_the_variables_of_the_other_formulas_too():
    # Premises bind x0 and x1; the conclusion counts x. Whole-problem fresh: x2 and x3.
    x0, x1 = Variable("x0"), Variable("x1")
    premises = [Quantifier("∃", x0, Atom("Q", [x0])), Quantifier("∃", x1, Atom("Q", [x1]))]
    _, goals, _ = _written(premises, Count("ge", Number(2), x, Atom("P", [x])))
    assert goals == ["(exists X2 (exists X3 ((P(X2) & P(X3)) & (X2 != X3))))."]


def test_two_counting_quantifiers_get_different_witnesses():
    assumptions, goals, _ = _written([Count("ge", Number(2), x, Atom("P", [x]))],
                                     Count("ge", Number(2), x, Atom("Q", [x])))
    assert assumptions == ["(exists X0 (exists X1 ((P(X0) & P(X1)) & (X0 != X1))))."]
    assert goals == ["(exists X2 (exists X3 ((Q(X2) & Q(X3)) & (X2 != X3))))."]


def test_a_nested_counting_quantifier_never_rebinds_a_name_of_its_scope():
    # ∃≥2 x ∃≥2 y R(x, y): the outer expansion copies the (already expanded) inner one once per
    # witness, and each copy binds its own two witnesses in a scope of its own; no binder is
    # inside the scope of a binder of the same name.
    inner = Count("ge", Number(2), y, Atom("R", [x, y]))
    _, goals, _ = _written([], Count("ge", Number(2), x, inner))
    assert _rebinds(goals[0]) == []
    assert goals[0].count("(exists ") == 2 + 2 * 2          # two outer witnesses, two per copy


def test_a_counting_quantifier_over_a_sort_is_expanded_the_same_way():
    # ∃≥2 x:S P(x): the matrix is guarded with S, then expanded. The premise binds x0, and the
    # non-emptiness fact of S (a closed sentence of its own) binds x1; the witnesses avoid both.
    from unicode_logic_kit.fol._msfl_nodes import SortedCount
    x0 = Variable("x0")
    assumptions, goals, _ = _written([Quantifier("∃", x0, Atom("Q", [x0]))],
                                     SortedCount("ge", Number(2), x, "S", Atom("P", [x])))
    assert assumptions == ["(exists X0 Q(X0)).", "(exists X1 S(X1))."]
    assert goals == ["(exists X2 (exists X3 (((S(X2) & P(X2)) & (S(X3) & P(X3))) & (X2 != X3))))."]


# --------------------------------------------------------------------------- #
# Random symbol sets.
# --------------------------------------------------------------------------- #

_WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _random_symbol_formulas(rng):
    names = ["P", "p", "Q", "f", "g", "a", "b", "Gaseous", "Rain", "θ", "theta", "2nd", "all", "exists", "v",
             "x y", "a.b", "é", "_u", "P2", "p2", "all2"]
    formulas = []
    for _ in range(rng.randint(1, 4)):
        parts = []
        for _ in range(rng.randint(1, 4)):
            kind = rng.choice(["atom", "fun", "const", "prop"])
            name = rng.choice(names)
            if kind == "prop":
                parts.append(Atom(name, []))
            elif kind == "const":
                parts.append(Atom("R", [Constant(name)]))
            elif kind == "fun":
                parts.append(Atom("R", [Function(name, [Constant("c")] * rng.randint(1, 3))]))
            else:
                parts.append(Atom(name, [Constant("c")] * rng.randint(1, 3)))
        formula = parts[0]
        for part in parts[1:]:
            formula = And(formula, part)
        formulas.append(formula)
    return formulas


def test_for_random_symbol_sets_the_tokens_are_distinct_words_and_a_lone_name_keeps_its_own():
    rng = random.Random(20261004)
    for _ in range(600):
        formulas = _random_symbol_formulas(rng)
        sanitised, names = _sanitize_for_prover9(formulas)
        tokens = list(names.symbols.values())
        assert len(tokens) == len(set(tokens)), names.symbols               # injective
        assert all(_WORD.fullmatch(token) for token in tokens), names.symbols   # a word Prover9 reads
        by_name = {}
        for (kind, name, arity), token in names.symbols.items():
            by_name.setdefault(name, []).append(((kind, arity), token))
        for name, entries in by_name.items():
            legal = bool(_WORD.fullmatch(name)) and name.isascii() and name not in ("all", "exists")
            variable_like = name[0] in "ABCDEFGHIJKLMNOPQRSTUVWXYZ_" if name else False
            for (kind, arity), token in entries:
                if len(entries) == 1 and legal and not (arity == 0 and variable_like):
                    assert token == name, (name, entries)                    # unchanged when lone
        # and the text of every sanitised formula is renderable
        for formula in sanitised:
            formula.to_prover9()


# --------------------------------------------------------------------------- #
# The real binary.
# --------------------------------------------------------------------------- #

_BINARY = Prover9Backend._binary()
_WSL = Prover9Backend._uses_wsl()
live = pytest.mark.skipif(
    not _BINARY,
    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or "
           "put 'prover9' on PATH; the text-level tests above carry the claim")


def _decide(goal, premises):
    return get_backend("prover9").decide(goal, premises, timeout=30000)


# name, premises, goal, "valid" or "invalid", why (derived by hand from the definition: one
# universe; a sort is a non-empty extension of the unary predicate of its name; c:S is an
# element of S; P(x) and P(x, y) are different relations).
_P = Atom
_c = Constant
_PROBLEMS = [
    ("two arities, unrelated", [_P("P", [_c("a")])], _P("P", [_c("a"), _c("b")]), "invalid",
     "U={0,1}, P/1={0}, P/2={}: the premise holds, P(a, b) does not"),
    ("two arities, both given", [_P("P", [_c("a")]), _P("P", [_c("a"), _c("b")])],
     _P("P", [_c("a"), _c("b")]), "valid", "the binary P(a, b) is a premise"),
    ("two arities, the unary one does not give the binary one",
     [_P("P", [_c("a"), _c("b")])], _P("P", [_c("a")]), "invalid",
     "U={0,1}, P/2={(0,1)}, P/1={}"),
    ("function at two arities", [_P("Q", [Function("f", [_c("a")])])],
     _P("Q", [Function("f", [_c("a"), _c("a")])]), "invalid",
     "f/1 and f/2 are unrelated functions: U={0,1}, f/1(a)=0, f/2(a,a)=1, Q={0}"),
    ("function at two arities, equal", [Atom("=", [Function("f", [_c("a")]), _c("b")]),
                                         Atom("=", [Function("f", [_c("a"), _c("a")]), _c("c")])],
     Atom("=", [Function("f", [_c("a")]), _c("b")]), "valid", "the first premise"),
    ("predicate and function of one name",
     [_P("f", [Function("f", [_c("a")])])], Quantifier("∃", x, _P("f", [x])), "valid",
     "the predicate f holds of the term f(a)"),
    ("predicate and function of one name, not the same thing",
     [Atom("=", [Function("f", [_c("a")]), _c("b")])], _P("f", [_c("b")]), "invalid",
     "f(a) = b says nothing about the predicate f"),
    ("predicate and constant of one name", [_P("p", [_c("p")])], Quantifier("∃", x, _P("p", [x])),
     "valid", "the constant p is in the predicate p"),
    ("proposition and predicate of one name", [Atom("p", [])], _P("p", [_c("a")]), "invalid",
     "the proposition p and the predicate p are unrelated"),
    ("constant and function of one name", [_P("P", [_c("a")])], _P("P", [Function("a", [_c("b")])]),
     "invalid", "the constant a and the function a/1 are unrelated"),
    ("sort and constant of one name (the constant is in the sort)",
     [SortedQuantifier("∀", x, "person", _P("P", [x]))], _P("P", [SortedConstant("person", "person")]),
     "valid", "person:person is an element of the sort person, and every person is P"),
    ("sort and constant of one name (a plain constant is not in the sort)",
     [SortedQuantifier("∀", x, "person", _P("P", [x]))], _P("P", [_c("person")]), "invalid",
     "U={0,1}, person={0}, P={0}, the constant person=1"),
    ("the sort is the unary predicate of its name",
     [], _P("person", [SortedConstant("carl", "person")]), "valid",
     "carl:person is an element of the sort person, which is the extension of the predicate person"),
    ("a predicate of the name of a sort at another arity is unrelated to the sort",
     [SortedQuantifier("∀", x, "S", _P("P", [x]))], _P("S", [_c("a"), _c("b")]), "invalid",
     "S/2 is no relation of the sort S: U={0,1}, S={0}, P={0}, S/2={}"),
    ("non-ASCII sort, non-empty", [SortedQuantifier("∀", x, "Größe", _P("P", [x]))],
     SortedQuantifier("∃", x, "Größe", _P("P", [x])), "valid", "a sort is never empty"),
    ("non-ASCII sort, not everything", [], SortedQuantifier("∀", x, "Größe", _P("P", [x])), "invalid",
     "U={0}, Größe={0}, P={}"),
    ("keyword sort all", [SortedQuantifier("∀", x, "all", _P("P", [x]))],
     _P("P", [SortedConstant("a", "all")]), "valid", "a:all is in the sort all"),
    ("keyword sort exists", [SortedQuantifier("∀", x, "exists", _P("P", [x]))],
     _P("P", [SortedConstant("a", "exists")]), "valid", "a:exists is in the sort exists"),
    # A formula in which the guard `exists(X)` is followed by an infix operator: read as the
    # quantifier `exists X` and a stray `&` when the sort keeps its name (the defect the
    # generated corpus found); ∃w:exists ∀x:Q c = d is a theorem of ∀x:Q c = d (take any w).
    ("keyword sort exists at the start of an operand",
     [SortedQuantifier("∀", x, "Q", Atom("=", [_c("c"), _c("d")]))],
     SortedQuantifier("∃", Variable("w"), "exists",
                      SortedQuantifier("∀", x, "Q", Atom("=", [_c("c"), _c("d")]))),
     "valid", "a sort is non-empty, and the premise does not mention w"),
    ("keyword sort all at the start of an operand",
     [SortedQuantifier("∀", x, "Q", Atom("=", [_c("c"), _c("d")]))],
     SortedQuantifier("∃", Variable("w"), "all",
                      SortedQuantifier("∀", x, "Q", Atom("=", [_c("c"), _c("d")]))),
     "valid", "a sort is non-empty, and the premise does not mention w"),
    ("keyword sort v", [SortedQuantifier("∀", x, "v", _P("P", [x]))],
     _P("P", [SortedConstant("a", "v")]), "valid", "a:v is in the sort v"),
    ("a sorted and a plain constant of one name", [_P("P", [_c("carl")]), _P("Q", [SortedConstant("carl", "A")])],
     SortedQuantifier("∃", x, "A", _P("P", [x])), "valid", "one constant carl; the sorted occurrence puts it in A"),
    ("a constant with two sorts", [_P("P", [SortedConstant("carl", "A")]), _P("Q", [SortedConstant("carl", "B")])],
     SortedQuantifier("∃", x, "A", _P("Q", [x])), "valid", "carl is in A and in B, and Q(carl)"),
]


@live
@pytest.mark.parametrize("name, premises, goal, verdict, reason", _PROBLEMS,
                         ids=[p[0] for p in _PROBLEMS])
def test_live_prover9_answers_a_problem_with_colliding_names_as_the_definition_says(
        name, premises, goal, verdict, reason):
    result = _decide(goal, premises)
    if verdict == "valid":
        assert result.status == "proved", (name, reason, result)
    else:
        # Prover9's exit does not certify invalidity: "no proof" is UNKNOWN / incomplete. What
        # matters is that the invalid ones are NOT proved, and that none is an input error.
        assert (result.status, result.reason) == ("unknown", "incomplete"), (name, reason, result)


# -- the generated corpus ---------------------------------------------------- #

_PREDICATES = [("P", 1), ("P", 2), ("Q", 0), ("Q", 1), ("R", 1), ("person", 1), ("person", 2),
               ("Human", 1), ("Human", 3), ("a b", 1), ("é", 1)]
_FUNCTIONS = [("f", 1), ("f", 2), ("g", 1), ("P", 1), ("person", 1)]
_CONSTANTS = ["a", "b", "f", "P", "Q", "person", "carl", "Gaseous", "theta", "θ"]
_SORTS = ["A", "Human", "Größe", "all", "exists", "v", "person", "Q", "a b"]
_SORTED_CONSTANTS = [("carl", "A"), ("carl", "person"), ("dora", "Human"), ("person", "person"),
                     ("f", "Größe"), ("Gaseous", "all"), ("a", "Q")]
_VARIABLES = "xyz"


def _term(rng, scope, depth=0):
    roll = rng.random()
    if scope and roll < 0.35:
        return Variable(rng.choice(scope))
    if roll < 0.6:
        return Constant(rng.choice(_CONSTANTS))
    if roll < 0.8:
        name, sort = rng.choice(_SORTED_CONSTANTS)
        return SortedConstant(name, sort)
    if depth == 0:
        name, arity = rng.choice(_FUNCTIONS)
        return Function(name, [_term(rng, scope, 1) for _ in range(arity)])
    return Constant(rng.choice(_CONSTANTS))


def _atom(rng, scope):
    if rng.random() < 0.15:
        return Atom("=", [_term(rng, scope), _term(rng, scope)])
    name, arity = rng.choice(_PREDICATES)
    return Atom(name, [_term(rng, scope) for _ in range(arity)])


def _formula(rng, scope, depth):
    if depth == 0 or rng.random() < 0.25:
        return _atom(rng, scope)
    roll = rng.random()
    if roll < 0.15:
        return Not(_formula(rng, scope, depth - 1))
    if roll < 0.55:
        return rng.choice((And, Or, Implies, Iff))(_formula(rng, scope, depth - 1),
                                                    _formula(rng, scope, depth - 1))
    free = [v for v in _VARIABLES if v not in scope]
    if not free:
        return _atom(rng, scope)
    body = _formula(rng, scope + [free[0]], depth - 1)
    kind = rng.choice("∀∃")
    if rng.random() < 0.55:
        return SortedQuantifier(kind, Variable(free[0]), rng.choice(_SORTS), body)
    return Quantifier(kind, Variable(free[0]), body)


def _substitute(node, name, term):
    if isinstance(node, Variable):
        return term if node.name == name else node
    return node.map_children(lambda child: _substitute(child, name, term))


def _problem(seed):
    """A premise list and a goal. Half are random; half have the SHAPE of an entailment (an
    instance of a universal, a generalisation of an instance), so that valid ones are common."""
    rng = random.Random(seed)
    if rng.random() < 0.4:
        premises = [_formula(rng, [], rng.choice((1, 2, 2))) for _ in range(rng.choice((0, 1, 1, 2)))]
        return premises, _formula(rng, [], rng.choice((1, 2, 2)))
    body = _formula(rng, ["w"], rng.choice((0, 1, 1)))
    sort = rng.choice(_SORTS)
    name, own = rng.choice(_SORTED_CONSTANTS)
    witness = rng.choice((SortedConstant(name, own), SortedConstant(name, own),
                          Constant(rng.choice(_CONSTANTS)),
                          Function("f", [Constant(rng.choice(_CONSTANTS))])))
    w = Variable("w")
    shape = rng.random()
    if shape < 0.4:
        return [SortedQuantifier("∀", w, sort, body)], _substitute(body, "w", witness)
    if shape < 0.55:
        return [Quantifier("∀", w, body)], _substitute(body, "w", witness)
    if shape < 0.9:
        return [_substitute(body, "w", witness)], SortedQuantifier("∃", w, sort, body)
    return [_substitute(body, "w", witness)], Quantifier("∃", w, body)


def _for_z3(node):
    """``node`` with every symbol given a name of its own, as the definition keeps them apart:
    ``P/1`` and ``P/2``, the predicate and the function ``f``, a constant, a sort (which is the
    unary predicate of its name). This is the oracle's own renaming: it shares nothing with the
    writer under test, and Z3 gets a problem in which no name has two meanings."""
    if isinstance(node, Atom):
        if node.predicate == "=":
            return Atom("=", [_for_z3(a) for a in node.args])
        return Atom(f"{node.predicate}@p{len(node.args)}", [_for_z3(a) for a in node.args])
    if isinstance(node, Function):
        return Function(f"{node.name}@f{len(node.args)}", [_for_z3(a) for a in node.args])
    if isinstance(node, Constant):
        return Constant(f"{node.name}@c")
    if isinstance(node, SortedConstant):
        return SortedConstant(f"{node.name}@c", f"{node.sort}@p1")
    if isinstance(node, SortedQuantifier):
        return SortedQuantifier(node.type, node.variable, f"{node.sort}@p1", _for_z3(node.formula))
    return node.map_children(_for_z3)


def _z3_answer(premises, goal):
    verdict = api.prove(_for_z3(goal), [_for_z3(p) for p in premises], backends=["z3"], timeout=20000)
    return verdict.status


def _corpus(first, count):
    return [_problem(seed) for seed in range(first, first + count)]


@live
def test_live_prover9_answers_generated_problems_with_colliding_names_as_z3_does():
    problems = _corpus(7000, 260)
    valid = invalid = skipped = 0
    for index, (premises, goal) in enumerate(problems):
        oracle = _z3_answer(premises, goal)
        if oracle not in ("proved", "refuted"):
            skipped += 1                              # a problem Z3 cannot settle is no data point
            continue
        result = _decide(goal, premises)
        text = (index, [p.to_unicode_str() for p in premises], goal.to_unicode_str(), result.status,
                result.reason, result.detail)
        # No problem ends as a Prover9 input error, and none is refused by the writer.
        assert result.status in ("proved", "unknown"), text
        assert result.reason not in ("unsupported", "infra"), text
        if oracle == "proved":
            valid += 1
            assert result.status == "proved", ("Z3 proves it, Prover9 does not", text)
        else:
            invalid += 1
            # Prover9 gives no answer for a non-theorem (it ends without a proof, or runs out of time
            # on an infinite search): what it must not do is prove it.
            assert result.status == "unknown" and result.reason in ("incomplete", "timeout"), (
                "Z3 refutes it, Prover9 must not prove it", text)
    # The corpus is not trivial: it has valid and invalid problems, and Z3 settles most of them.
    assert valid >= 50 and invalid >= 50 and skipped <= 40, (valid, invalid, skipped)


def _naive_text(premises, goal):
    """The text a caller gets by joining the single-node renderers: no whole-problem view."""
    return ("set(prolog_style_variables).\nformulas(assumptions).\n"
            + "".join(f"  {p.to_prover9()}.\n" for p in premises)
            + "end_of_list.\nformulas(goals).\n  " + goal.to_prover9() + ".\nend_of_list.\n")


@live
def test_live_control_the_same_problems_written_node_by_node_are_refused():
    # The control: this is what the writer is for. Written without a whole-problem view, a
    # problem in which a name has two symbols is refused by Prover9 (or by the single renderer,
    # for a name that is no word). It shows the corpus above can see the defect.
    refused = 0
    for premises, goal in _corpus(7000, 80):
        try:
            text = _naive_text(premises, goal)
            p9._run_prover9(text, _BINARY, timeout=30, raise_on_rejection=True, use_wsl=_WSL)
        except (Prover9Rejected, NotImplementedError):
            refused += 1
    assert refused >= 25, refused


def test_the_generated_corpus_exercises_every_kind_of_collision():
    # A property of the generator, checked without Prover9: across the corpus a name occurs at
    # two arities, as a predicate and as a function, as a predicate and as a constant, as a sort
    # and as a constant, and a sorted and a plain constant share a name.
    seen = set()
    for premises, goal in _corpus(7000, 260):
        symbols = {}
        sorts = set()
        plain, sorted_names = set(), set()
        for formula in premises + [goal]:
            for node in formula.walk():
                if isinstance(node, Atom) and node.predicate != "=":
                    symbols.setdefault(node.predicate, set()).add(("predicate", len(node.args)))
                elif isinstance(node, Function):
                    symbols.setdefault(node.name, set()).add(("function", len(node.args)))
                elif isinstance(node, Constant):
                    symbols.setdefault(node.name, set()).add(("function", 0))
                    plain.add(node.name)
                elif isinstance(node, SortedConstant):
                    symbols.setdefault(node.name, set()).add(("function", 0))
                    sorted_names.add(node.name)
                    sorts.add(node.sort)
                elif isinstance(node, SortedQuantifier):
                    sorts.add(node.sort)
        for name, entries in symbols.items():
            kinds = {kind for kind, _ in entries}
            arities = {(kind, arity) for kind, arity in entries}
            if len({a for k, a in arities if k == "predicate"}) > 1:
                seen.add("predicate at two arities")
            if len({a for k, a in arities if k == "function" and a > 0}) > 1:
                seen.add("function at two arities")
            if kinds == {"predicate", "function"}:
                seen.add("predicate and function")
            if ("function", 0) in entries and any(k == "predicate" for k, _ in entries):
                seen.add("predicate and constant")
            if name in sorts and ("function", 0) in entries:
                seen.add("sort and constant")
        if plain & sorted_names:
            seen.add("sorted and plain constant")
        if any(not sort.isascii() for sort in sorts):
            seen.add("non-ASCII sort")
        if sorts & {"all", "exists", "v"}:
            seen.add("keyword sort")
    assert seen == {"predicate at two arities", "function at two arities", "predicate and function",
                    "predicate and constant", "sort and constant", "sorted and plain constant",
                    "non-ASCII sort", "keyword sort"}, seen
