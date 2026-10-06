r"""Prover9 reads an upper-case-initial symbol in term position as a VARIABLE.

Every Prover9 file this kit writes sets ``prolog_style_variables``. Under that
flag Prover9 decides, per symbol and after reading the whole input, whether a
symbol is a variable: LADR's ``variable_name`` (``ladr/symbols.c``) is, for the
prolog style, ``*s >= 'A' && *s <= 'Z'``, and the manual says the same ("If this
flag is set, variables in clauses start with (upper case) 'A' through 'Z'").
``set_vars_recurse`` (``ladr/term.c``) applies it to every ARITY-0 term, so a
CONSTANT is read as a variable when its name starts upper-case, while a function
or a predicate WITH arguments is not (only its arguments are examined).

So the file for the premise ``P(Gaseous)`` and the goal ``P(c)``

    formulas(assumptions).
      P(Gaseous).
    formulas(goals).
      P(c).

says "for all X, P(X)" and then asks for P(c): Prover9 proves it. Hand-derived:
``P(Gaseous)`` with ``Gaseous`` a constant does NOT entail ``P(c)`` (interpret P
as {the denotation of Gaseous}, c as another element). An ontology individual
looks exactly like ``Gaseous``.

No Prover9 binary is needed for almost everything here. What Prover9 reads is
fixed by its documented rule, which :func:`_variables_in` below applies to the
TEXT the writer produced (the kit's own reader, ``parse_prover9``, follows the
same convention and is the second oracle). One live test runs the real binary
(natively, or inside WSL when ``$UFK_PROVER9_WSL=1``) and skips, with a reason,
when there is none; ``tests/test_prover9_quoting.py`` compares the real binary
with Z3 on the single-node renderers.

What is pinned:

* the problem writer RENAMES such a constant (lower-case initial, injective over
  the whole problem, recorded in the name map) and does not touch what Prover9
  reads correctly: predicates and functions with arguments;
* ``Constant.to_prover9()`` alone cannot rename, so it writes the name in DOUBLE
  QUOTES (``"Gaseous"``), which Prover9 never reads as a variable, and refuses,
  by name, only a name that cannot stand in quotes;
* the same for a NULLARY predicate, which is an arity-0 term too: ``Rain`` is
  written ``rain`` by the writer, ``"Rain"`` by the single node, and the rename is
  recorded in ``nullary_predicates``;
* the writer's own calls never reach the quoting branch (a randomised proof);
* the mirror: a kit VARIABLE is never rendered so that it reads as a constant,
  and a constant is never rendered so that it can collide with a variable.
"""

import random
import re
import string

import pytest

from unicode_fol_kit.atp import prover9_entailment as p9
from unicode_fol_kit.atp.prover9_entailment import (
    check_logical_entailment, generate_prover9_input_with_mapping,
)
from unicode_fol_kit.atp.protocol import Prover9Backend
from unicode_fol_kit.fol._msfl_nodes import SortedConstant, SortedQuantifier
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Implies, Not, Or, Quantifier, Variable,
)
from unicode_fol_kit.fol.prover9_input import parse_prover9


def P(*args):
    return Atom("P", list(args))


def _formula_lines(text):
    """The bare formulas of a written problem, assumptions first, then the goal."""
    lines = []
    for line in text.splitlines():
        stripped = line.strip()
        if (stripped.endswith(".") and stripped != "end_of_list."
                and not stripped.startswith(("set(", "clear(", "formulas("))):
            lines.append(stripped[:-1])
    return lines


_SYMBOL = re.compile(r"[A-Za-z0-9_$]+")


def _variables_in(formula_text, rendered_variables=frozenset()):
    """The arity-0 term symbols of ``formula_text`` that Prover9 reads as VARIABLES,
    minus the ones the kit itself rendered as variables (``rendered_variables``).

    LADR's rule, applied literally: a symbol is a variable iff its first character
    is A..Z (the kit also counts a leading underscore, defensively). A symbol
    followed by ``(`` is a function/predicate with arguments and is not examined;
    the quantifier words are not symbols. A double-quoted symbol is stored by
    Prover9 with its quotes, so it is never a variable and is skipped whole.
    """
    formula_text = re.sub(r'"[^"]*"', '"~"', formula_text)
    found = []
    for match in _SYMBOL.finditer(formula_text):
        symbol = match.group()
        if formula_text[match.end():match.end() + 1] == "(" or symbol in ("all", "exists"):
            continue
        if symbol in rendered_variables:
            continue
        if symbol[0] in string.ascii_uppercase or symbol[0] == "_":
            found.append(symbol)
    return found


def test_the_oracle_flags_the_text_this_file_exists_for():
    # The control: the pre-fix text for P(Gaseous) is flagged, the fixed one is not.
    assert _variables_in("P(Gaseous)") == ["Gaseous"]
    assert _variables_in("P(gaseous)") == []
    # A capitalised predicate or function WITH arguments is not a variable.
    assert _variables_in("Human(Mother(c))") == []
    # What the kit renders as a variable is not counted.
    assert _variables_in("(all X (P(X, c)))", frozenset({"X"})) == []
    assert _variables_in("(all X (P(X, _x)))", frozenset({"X"})) == ["_x"]
    # A double-quoted symbol is never a variable.
    assert _variables_in('P("Gaseous")') == [] and _variables_in('("Rain" & "Wet")') == []


# --------------------------------------------------------------------------- #
# (a) the writer renames a constant Prover9 would read as a variable.
# --------------------------------------------------------------------------- #

def test_an_upper_case_constant_is_renamed_so_the_premise_is_not_read_as_forall():
    text, mapping = generate_prover9_input_with_mapping([P(Constant("Gaseous"))], P(Constant("c")))
    # Hand-derived: the premise names the CONSTANT Gaseous, spelled with a
    # lower-case initial so Prover9 reads a constant; the goal is untouched.
    assert _formula_lines(text) == ["P(gaseous)", "P(c)"]
    assert "Gaseous" not in text
    assert mapping.constants == {"Gaseous": "gaseous"}
    assert mapping.mapping["Gaseous"] == "gaseous"
    assert mapping.reverse()["gaseous"] == "Gaseous"
    assert all(_variables_in(line) == [] for line in _formula_lines(text))


def test_the_old_text_proved_a_non_theorem_and_the_new_text_does_not():
    # Z3 as the independent oracle for what each reading means. ForAll X. P(X)
    # entails P(c); P(Gaseous) with Gaseous a constant does not.
    import z3

    from unicode_fol_kit.fol._fol_nodes import Z3Env

    def entails(premise, goal):
        env = Z3Env()
        solver = z3.Solver()
        solver.add(premise.to_z3(env), z3.Not(goal.to_z3(env)))
        return solver.check() == z3.unsat

    x = Variable("x")
    as_prover9_read_it = Quantifier("∀", x, P(x))                # `P(Gaseous)` under prolog_style_variables
    as_the_formula_says = P(Constant("Gaseous"))
    assert entails(as_prover9_read_it, P(Constant("c")))
    assert not entails(as_the_formula_says, P(Constant("c")))
    # And the reader the kit shares with Prover9's convention agrees about the text.
    assert parse_prover9("P(Gaseous)") == P(Variable("gaseous"))
    assert parse_prover9("P(gaseous)") == P(Constant("gaseous"))


def N(name):
    """A bare (nullary) atom: a proposition such as ``Rain``."""
    return Atom(name, [])


def test_an_upper_case_nullary_predicate_is_renamed_so_it_is_not_read_as_a_variable():
    # Hand-derived: Rain and Wind are arity-0 terms that start A..Z, so under
    # prolog_style_variables LADR reads each as a variable (the atom itself is the
    # arity-0 term set_vars_recurse examines; measured on Prover9 2026-8A: the bare
    # `Rain` is refused as a variable). Spelled with a lower-case initial they are
    # read as propositions.
    text, mapping = generate_prover9_input_with_mapping([N("Rain")], N("Wind"))
    assert _formula_lines(text) == ["rain", "wind"]
    assert mapping.nullary_predicates == {"Rain": "rain", "Wind": "wind"}
    assert mapping.constants == {}
    assert mapping.reverse() == {"rain": "Rain", "wind": "Wind"}
    assert all(_variables_in(line) == [] for line in _formula_lines(text))
    # The control: the text before the rename is flagged by the oracle.
    assert _variables_in("Rain") == ["Rain"]


def test_the_same_word_as_a_nullary_predicate_and_as_one_with_arguments():
    # Hand-derived: Rain(X) has an argument, so Prover9 reads a predicate and the
    # name is not renamed; the bare Rain is an arity-0 term and is.
    rain_x = Quantifier("∀", Variable("x"), Atom("Rain", [Variable("x")]))
    text, mapping = generate_prover9_input_with_mapping([rain_x], N("Rain"))
    assert _formula_lines(text) == ["(all X Rain(X))", "rain"]
    assert mapping.mapping["Rain"] == "Rain"
    assert mapping.nullary_predicates == {"Rain": "rain"}
    assert mapping.reverse() == {"Rain": "Rain", "rain": "Rain"}


def test_a_renamed_nullary_predicate_never_shares_a_token_with_another_name():
    # Hand-derived with the documented numeric-suffix scheme (the constants'
    # Gaseous -> gaseous2): `rain` is already a legal nullary predicate and is
    # reserved in pass one, so Rain takes the next free spelling.
    text, mapping = generate_prover9_input_with_mapping([N("rain"), N("Rain")], N("c"))
    assert _formula_lines(text) == ["rain", "rain2", "c"]
    assert mapping.nullary_predicates == {"Rain": "rain2"}
    assert mapping.reverse()["rain2"] == "Rain"


def test_a_nullary_predicate_and_a_constant_of_one_spelling_are_two_symbols():
    # The proposition Rain and the individual Rain: in Prover9 both would be the
    # arity-0 symbol `Rain`, so the two must not be written with one spelling.
    text, mapping = generate_prover9_input_with_mapping([N("Rain")], P(Constant("Rain")))
    proposition, individual = mapping.nullary_predicates["Rain"], mapping.constants["Rain"]
    assert proposition != individual
    assert _formula_lines(text) == [proposition, f"P({individual})"]
    assert mapping.reverse()[proposition] == mapping.reverse()[individual] == "Rain"
    assert all(_variables_in(line) == [] for line in _formula_lines(text))


def test_an_underscore_initial_nullary_predicate_is_renamed_too():
    # The same treatment as an underscore-initial constant (_x -> c_x).
    text, mapping = generate_prover9_input_with_mapping([N("_p")], N("c"))
    assert _formula_lines(text) == ["c_p", "c"]
    assert mapping.nullary_predicates == {"_p": "c_p"}


def test_infix_predicates_and_lower_case_nullary_predicates_are_left_alone():
    text, mapping = generate_prover9_input_with_mapping(
        [Atom("=", [Constant("a"), Constant("b")])], N("rain"))
    assert _formula_lines(text) == ["(a = b)", "rain"]
    assert mapping.nullary_predicates == {}


def test_a_predicate_and_a_function_with_arguments_are_not_renamed():
    # Hand-derived: Human and Mother are Capitalised but carry arguments, so
    # Prover9 reads them as predicate/function symbols; only the arity-0 term Eve
    # is a variable-shaped symbol. The goal already uses the legal constant eve,
    # so Eve (a different constant) cannot take that token: it becomes eve2.
    premise = Atom("Human", [Function("Mother", [Constant("Eve")])])
    text, mapping = generate_prover9_input_with_mapping([premise], Atom("Human", [Constant("eve")]))
    assert _formula_lines(text) == ["Human(Mother(eve2))", "Human(eve)"]
    assert mapping.mapping["Human"] == "Human" and mapping.mapping["Mother"] == "Mother"
    assert mapping.constants == {"Eve": "eve2"}


def test_a_renamed_constant_never_shares_a_token_with_another_name():
    # Hand-derived with the documented numeric-suffix scheme: pass one reserves
    # every already-legal name (P, gaseous, Q, c), pass two gives each variable-
    # shaped constant a lower-cased first letter, then a numeric suffix if taken.
    # Gaseous -> base gaseous (taken) -> gaseous2; GASEOUS -> base gASEOUS (free).
    premises = [P(Constant("gaseous")), P(Constant("Gaseous")), P(Constant("GASEOUS"))]
    text, mapping = generate_prover9_input_with_mapping(premises, Atom("Q", [Constant("c")]))
    assert _formula_lines(text) == ["P(gaseous)", "P(gaseous2)", "P(gASEOUS)", "Q(c)"]
    tokens = [mapping.get_constant(n) for n in ("gaseous", "Gaseous", "GASEOUS")]
    assert len(set(tokens)) == 3
    assert mapping.reverse()["gaseous2"] == "Gaseous"
    assert mapping.reverse()["gASEOUS"] == "GASEOUS"


def test_a_word_that_is_both_a_class_and_an_individual_gets_two_tokens():
    # An OWL pun: the class Person and the individual Person. The predicate keeps
    # its Capitalised spelling (Prover9 reads it correctly); the constant does not.
    premises = [Atom("Person", [Constant("Person")]), Atom("Person", [Constant("person")])]
    text, mapping = generate_prover9_input_with_mapping(premises, Atom("Person", [Constant("bob")]))
    # Hand-derived: `person` is a legal constant and reserved first, so the
    # individual Person becomes person2.
    assert _formula_lines(text) == ["Person(person2)", "Person(person)", "Person(bob)"]
    assert mapping.mapping["Person"] == "Person"             # the predicate
    assert mapping.constants == {"Person": "person2"}        # the individual
    assert mapping.reverse() == {"Person": "Person", "person": "person", "bob": "bob",
                                 "person2": "Person"}


def test_an_underscore_initial_constant_is_renamed_too():
    # The LADR source reads only A..Z as variable-initial, but this kit's own
    # reader and the Prolog convention read `_x` as one; renaming costs nothing
    # where Prover9 would not have, and is what keeps the text safe where it would.
    text, mapping = generate_prover9_input_with_mapping([P(Constant("_x"))], P(Constant("c")))
    assert _formula_lines(text) == ["P(c_x)", "P(c)"]
    assert mapping.constants == {"_x": "c_x"}
    # A non-ASCII name that transliterates to an underscore start gets the same treatment.
    text, mapping = generate_prover9_input_with_mapping([P(Constant("_é"))], P(Constant("c")))
    assert _formula_lines(text) == ["P(c_u00e9)", "P(c)"]


def test_equality_and_a_sorted_constant_are_covered_too():
    eq = Atom("=", [Constant("Gaseous"), Constant("c")])
    text, _ = generate_prover9_input_with_mapping([eq], P(Constant("c")))
    assert _formula_lines(text) == ["(gaseous = c)", "P(c)"]

    # A SortedConstant renders as the plain constant of the same name (the sorted
    # route lowers it with to_fol), so it has to be renamed in step.
    sorted_premise = SortedQuantifier("∀", Variable("x"), "Phase",
                                      P(Variable("x"), SortedConstant("Gaseous", "Phase")))
    text, mapping = generate_prover9_input_with_mapping([sorted_premise], P(Constant("c")))
    # ∀x:S φ lowers to ∀x (S(x) → φ).
    assert _formula_lines(text)[0] == "(all X (Phase(X) -> P(X, gaseous)))"
    assert "Gaseous" not in text
    assert mapping.constants == {"Gaseous": "gaseous"}
    assert any(line.startswith("(exists ") and "Phase(" in line for line in _formula_lines(text))


def test_what_prover9_is_given_by_check_logical_entailment_has_the_constant_renamed(monkeypatch):
    seen = {}

    def fake_run(prover_input, path, timeout=30, raise_on_rejection=False,
                 raise_on_timeout=False, use_wsl=False):
        seen["input"] = prover_input
        return False

    monkeypatch.setattr(p9, "_run_prover9", fake_run)
    assert check_logical_entailment([P(Constant("Gaseous"))], P(Constant("c")), "prover9") is False
    assert _formula_lines(seen["input"]) == ["P(gaseous)", "P(c)"]


# --------------------------------------------------------------------------- #
# (b) the single node cannot rename, so it writes the name in double quotes.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", ["Gaseous", "X", "A1", "_x", "__y"])
def test_a_constant_rendered_alone_is_written_in_quotes_when_prover9_would_read_a_variable(name):
    # Hand-derived. A bare `Gaseous` is a variable under prolog_style_variables, so the
    # text P(Gaseous) says "for all X, P(X)"; a double-quoted symbol is stored by
    # Prover9 WITH its quotes, so its first character is the quote and never a
    # variable. (This test used to expect a refusal of these five names: that was the
    # only safe thing to do before the quoting was known to work.)
    quoted = f'"{name}"'
    for node, text in ((Constant(name), quoted),
                       (P(Constant(name)), f"P({quoted})"),
                       (And(P(Constant(name)), P(Constant("c"))), f"(P({quoted}) & P(c))"),
                       (Quantifier("∀", Variable("x"), Atom("R", [Variable("x"), Constant(name)])),
                        f"(all X R(X, {quoted}))"),
                       (Atom("=", [Constant(name), Constant("c")]), f"({quoted} = c)"),
                       (P(Function("f", [Constant(name)])), f"P(f({quoted}))"),
                       (SortedConstant(name, "S"), quoted)):
        assert node.to_prover9() == text
        # No arity-0 symbol of the text is a variable but the ones the kit rendered as such.
        assert _variables_in(text, frozenset({"X"})) == []
    # The oracle sees a quoted symbol as a symbol of its own: it flags the bare spelling
    # and nothing but the bare spelling.
    assert _variables_in(f"P({name})") == [name]


@pytest.mark.parametrize("name", ['Gas"eous', "Gas eous", "Gas.eous", "_x y"])
def test_a_constant_rendered_alone_is_refused_when_it_would_be_a_variable_and_cannot_be_quoted(name):
    # LADR has no escape for a double quote inside quotes, and a name with a space or a
    # full stop is not a symbol the kit's reader can read back; bare, each of these
    # would be read as a variable (or as several symbols). The refusal names the
    # constant, says why, and points at the problem writer, which renames it.
    for node in (Constant(name), P(Constant(name)), And(P(Constant(name)), P(Constant("c"))),
                 Atom("=", [Constant(name), Constant("c")]), SortedConstant(name, "S")):
        with pytest.raises(NotImplementedError) as excinfo:
            node.to_prover9()
        message = str(excinfo.value)
        assert repr(name) in message                              # names the constant
        assert "prolog_style_variables" in message and "VARIABLE" in message   # says why
        assert "double quotes" in message                         # and what was tried
        assert "generate_prover9_input_with_mapping" in message   # and where to go instead


@pytest.mark.parametrize("name, text", [
    ("gaseous", "gaseous"), ("c", "c"), ("x", "x"), ("c_Liquid", "c_Liquid"),
    ("dani_Shapiro", "dani_Shapiro"),
    # Greek and non-ASCII names are transliterated to a LOWER-case token before the
    # rule is applied: theta, and the codepoint escape u015a / u0398 -- not variables.
    ("θ", "theta"), ("Ś", "u015a"), ("Θ", "u0398"),
    # Digit-leading is not a variable (and is made legal by the writer, as before).
    ("2008SummerOlympics", "2008SummerOlympics"),
])
def test_a_constant_that_prover9_reads_as_a_constant_is_rendered_as_before(name, text):
    assert Constant(name).to_prover9() == text
    assert P(Constant(name)).to_prover9() == f"P({text})"


def test_the_mcp_render_tool_writes_an_upper_case_constant_in_quotes_and_reports_a_refusal_as_an_error():
    from unicode_fol_kit.mcp import server

    # An upper-case constant cannot be spelled in the unicode grammar, but it can
    # arrive through a quoted TPTP word: 'Gaseous'. The single-node renderer writes it
    # in double quotes (it used to refuse it: the quoting makes that needless)...
    assert (server.render("fof(a, axiom, p('Gaseous')).", to="prover9", dialect="tptp")["rendered"]
            == 'P("Gaseous")')
    # ... and still refuses, as a structured error, a name that would be a variable and
    # cannot stand in quotes: the TPTP word 'Gas eous' has a space in it.
    refused = server.render("fof(a, axiom, p('Gas eous')).", to="prover9", dialect="tptp")
    assert refused["error"]["type"] == "NotImplementedError"
    assert "'Gas eous'" in refused["error"]["message"]
    assert "generate_prover9_input_with_mapping" in refused["error"]["message"]
    # The same formula still renders for the targets that do not read it as a variable...
    assert server.render("fof(a, axiom, p('Gaseous')).", to="tptp", dialect="tptp")["rendered"] == "p(gaseous)"
    # ...and a lower-case constant is untouched.
    assert server.render("fof(a, axiom, p(gaseous)).", to="prover9", dialect="tptp")["rendered"] == "P(gaseous)"


# --------------------------------------------------------------------------- #
# The writer's own calls never reach the quoting branch: a randomised proof.
#
# After _sanitize_for_prover9 no constant of the problem is variable-shaped, so
# Constant.to_prover9() cannot quote (or refuse) inside the writer: the written
# problem holds no double quote at all. Checked on formulas built from a pool of
# names that includes every troublesome shape, by (1) the writer not raising, (2)
# the LADR rule applied to the TEXT finding no variable-shaped constant, and (3) the
# text read back by the kit's own reader and mapped through the name map being
# exactly the formula that went in.
# --------------------------------------------------------------------------- #

_CONSTANTS = ["a", "b", "gaseous", "Gaseous", "GASEOUS", "X", "A1", "_x", "__y", "Person",
              "person", "Ś", "θ", "Θ", "2008SummerOlympics", "dani_Shapiro", "c_u00e9", "é"]
_PREDICATES = ["P", "Q", "Human", "Person"]
_FUNCTIONS = ["f", "Mother", "Person", "g"]
# Bare atoms (propositions). None of these is also a constant of the pool, so no
# word is an arity-0 predicate and an arity-0 constant at once.
_PROPOSITIONS = ["Rain", "rain", "Wet", "_p", "Ŵ", "P"]


def _term(rng, depth, variables):
    roll = rng.random()
    if variables and roll < 0.2:
        return rng.choice(variables)
    if depth > 0 and roll < 0.5:
        return Function(rng.choice(_FUNCTIONS), [_term(rng, depth - 1, variables)
                                                 for _ in range(rng.randint(1, 2))])
    return Constant(rng.choice(_CONSTANTS))


def _formula(rng, depth, variables):
    roll = rng.random()
    if depth == 0 or roll < 0.35:
        if rng.random() < 0.15:
            return Atom("=", [_term(rng, 1, variables), _term(rng, 1, variables)])
        if rng.random() < 0.12:
            return Atom(rng.choice(_PROPOSITIONS), [])
        return Atom(rng.choice(_PREDICATES), [_term(rng, 1, variables)
                                              for _ in range(rng.randint(1, 3))])
    if roll < 0.5:
        return Not(_formula(rng, depth - 1, variables))
    if roll < 0.8:
        connective = rng.choice((And, Or, Implies))
        return connective(_formula(rng, depth - 1, variables), _formula(rng, depth - 1, variables))
    variable = Variable(rng.choice("xyz"))
    return Quantifier(rng.choice("∀∃"), variable,
                      _formula(rng, depth - 1, variables + [variable]))


def _unmap(node, reverse):
    """The original-name image of a formula read back from the written text."""
    if isinstance(node, Atom):
        name = node.predicate if node.predicate in Atom.INFIX_PREDS_P9 else reverse.get(node.predicate, node.predicate)
        return Atom(name, [_unmap(a, reverse) for a in node.args])
    if isinstance(node, Function):
        name = node.name if node.name in Function.INFIX_OPS else reverse.get(node.name, node.name)
        return Function(name, [_unmap(a, reverse) for a in node.args])
    if isinstance(node, Constant):
        return Constant(reverse.get(node.name, node.name))
    return node.map_children(lambda child: _unmap(child, reverse))


# The variables a written formula may hold: the upper case of the three the generator binds, and of the
# fresh names the writer gives a binder that sits inside the scope of one of its own name (x0, y1, ...).
_WRITTEN_VARIABLES = frozenset({"X", "Y", "Z"} | {f"{v}{i}" for v in "XYZ" for i in range(60)})


def _rebinds_a_name(node, enclosing=frozenset()):
    """Whether a binder of the formula sits inside the scope of a binder of the same name."""
    if isinstance(node, Quantifier):
        if node.variable.name in enclosing:
            return True
        enclosing = enclosing | {node.variable.name}
    return any(_rebinds_a_name(child, enclosing) for child in node._child_nodes())


def _alpha_normal(node, scope=()):
    """``node`` with every bound variable named by the depth of its binder, so that two formulas that
    differ only in the names of their bound variables (alpha-conversion) have one normal form."""
    if isinstance(node, Quantifier):
        name = f"#{len(scope)}"
        return Quantifier(node.type, Variable(name),
                          _alpha_normal(node.formula, scope + ((node.variable.name, name),)))
    if isinstance(node, Variable):
        for original, bound in reversed(scope):
            if original == node.name:
                return Variable(bound)
        return node
    return node.map_children(lambda child: _alpha_normal(child, scope))


def test_the_writers_own_calls_never_reach_the_quoting_branch_and_never_write_a_variable_constant():
    rng = random.Random(20261004)
    seen_upper = seen_pun = seen_proposition = seen_rebound = 0
    for _ in range(400):
        premises = [_formula(rng, 3, []) for _ in range(rng.randint(0, 3))]
        conclusion = _formula(rng, 3, [])
        text, mapping = generate_prover9_input_with_mapping(premises, conclusion)   # (1) never raises
        assert text.isascii()
        assert '"' not in text          # the rename, not the quoting, is what keeps a name from being a variable
        originals = list(premises) + [conclusion]
        written = _formula_lines(text)
        assert len(written) == len(originals)
        reverse = mapping.reverse()
        for original, line in zip(originals, written):
            assert _variables_in(line, _WRITTEN_VARIABLES) == [], line      # (2) the LADR rule on the text
            read_back = _unmap(parse_prover9(line), reverse)
            # (3) read-back: exactly the formula that went in; up to the names of the bound variables when
            # the formula binds a name inside the scope of a binder of that name (the writer renames the
            # inner binder, so that LADR does not, to a symbol that a constant may have).
            if _rebinds_a_name(original):
                seen_rebound += 1
                assert _alpha_normal(read_back) == _alpha_normal(original), (line, original)
            else:
                assert read_back == original, (line, original)
        names = {n.name for f in originals for n in f.walk() if isinstance(n, Constant)}
        seen_upper += any(n[0] in string.ascii_uppercase or n[0] == "_" for n in names)
        seen_pun += bool(names & ({n.predicate for f in originals for n in f.walk() if isinstance(n, Atom)}
                                  | {n.name for f in originals for n in f.walk() if isinstance(n, Function)}))
        propositions = {n.predicate for f in originals for n in f.walk()
                        if isinstance(n, Atom) and not n.args and n.predicate not in Atom.INFIX_PREDS_P9}
        seen_proposition += any(p[0] in string.ascii_uppercase or p[0] == "_" for p in propositions)
        # (2) above already shows no bare atom is written as a variable-shaped
        # symbol; here, distinct propositions keep distinct tokens.
        written_propositions = [mapping.get_nullary(p) for p in propositions]
        assert len(set(written_propositions)) == len(written_propositions)
        # No two original constants share a written token (injectivity over the problem).
        tokens = [mapping.get_constant(n) for n in names]
        assert len(set(tokens)) == len(tokens)
    assert seen_upper > 100 and seen_pun > 10        # the generator really exercises both
    assert seen_rebound > 20                          # ... and formulas with a re-bound binder
    assert seen_proposition > 50                      # ... and the bare upper-case atoms


# --------------------------------------------------------------------------- #
# (c) the mirror, by measurement.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("digits", ["", "0", "12"])
@pytest.mark.parametrize("letter", list(string.ascii_lowercase))
def test_a_variable_of_the_kits_grammar_is_always_rendered_as_a_prover9_variable(letter, digits):
    # The VARIABLE terminal is one term-valued letter plus ASCII digits. For an
    # ASCII letter the rendering is its upper-case form: first character A..Z,
    # which is a variable under prolog_style_variables, whatever the digits.
    name = letter + digits
    text = Variable(name).to_prover9()
    assert text == name.upper()
    assert text[0] in string.ascii_uppercase


@pytest.mark.parametrize("name", ["ı", "ſ", "ß", "é", "中", "ﬅ", "ﬆ"])
def test_a_variable_with_a_non_ascii_letter_is_refused_not_merged_with_another(name):
    # 'ı'.upper() is 'I' and 'ſ'.upper() is 'S': the text for the variable ı is the
    # text for i. 'ß' gives 'SS', the ligatures ﬅ and ﬆ both give 'ST'; 'é' and '中'
    # give non-ASCII text Prover9 cannot read. None of that may be written.
    with pytest.raises(NotImplementedError, match="non-ASCII") as excinfo:
        Variable(name).to_prover9()
    assert repr(name) in str(excinfo.value)


def test_two_different_variables_are_never_written_as_one():
    # Before the refusal this printed `(all I (all I R(I, I)))`: the inner binder
    # captured both arguments, a different formula.
    formula = Quantifier("∀", Variable("i"),
                         Quantifier("∀", Variable("ı"), Atom("R", [Variable("ı"), Variable("i")])))
    with pytest.raises(NotImplementedError, match="non-ASCII"):
        formula.to_prover9()


def test_no_constant_can_be_written_so_that_it_collides_with_a_written_variable():
    # A written variable starts with A..Z (previous tests). A constant is written
    # either lower-case-initial (the writer) or in double quotes (the leaf), so the
    # two sets of spellings are disjoint: checked over every shape of the pool.
    variables = {Variable(c + d).to_prover9() for c in string.ascii_lowercase for d in ("", "0", "12")}
    for name in _CONSTANTS:
        _, mapping = generate_prover9_input_with_mapping([], P(Constant(name)))
        token = mapping.get_constant(name)
        assert token not in variables and token[0] not in string.ascii_uppercase + "_"
        leaf = Constant(name).to_prover9()
        assert leaf not in variables
        assert leaf[0] == '"' or leaf[0] not in string.ascii_uppercase + "_"


# --------------------------------------------------------------------------- #
# The real binary, when there is one.
# --------------------------------------------------------------------------- #

def _prover9_binary():
    """The binary the backend would use: ``$UFK_PROVER9`` (a path inside WSL when
    ``$UFK_PROVER9_WSL=1``), else ``prover9`` on PATH."""
    return Prover9Backend._binary()


@pytest.mark.skipif(not _prover9_binary(),
                    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with "
                           "$UFK_PROVER9_WSL=1) or put 'prover9' on PATH; the text-level "
                           "tests above carry the claim")
def test_live_prover9_does_not_prove_p_c_from_p_gaseous():
    binary = _prover9_binary()
    use_wsl = Prover9Backend._uses_wsl()
    gaseous, c = P(Constant("Gaseous")), P(Constant("c"))
    # Hand-derived: P(Gaseous) does not entail P(c) for a constant Gaseous...
    assert check_logical_entailment([gaseous], c, binary, use_wsl=use_wsl) is False
    # ...but does entail itself, and ∀x P(x) entails P(c) (the old reading, written correctly).
    assert check_logical_entailment([gaseous], gaseous, binary, use_wsl=use_wsl) is True
    assert check_logical_entailment([Quantifier("∀", Variable("x"), P(Variable("x")))], c, binary,
                                    use_wsl=use_wsl) is True
