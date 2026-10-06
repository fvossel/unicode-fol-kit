r"""A symbol Prover9 would read as a VARIABLE is written in double quotes.

Every Prover9 file this kit writes sets ``prolog_style_variables``. Under that flag
LADR reads an arity-0 symbol that begins with ``A``..``Z`` as a VARIABLE
(``ladr/symbols.c``, ``variable_name``), an atom with no arguments included. Measured
on Prover9 2026-8A: the file ``P(Gaseous)`` with the goal ``P(c)`` is PROVED (it says
"for all X, P(X)"), and a bare ``Rain`` is refused ("cannot be used as atomic
formulas, because they are variables"). LADR stores a DOUBLE-QUOTED symbol with its
quote characters, so the first character it tests is the quote: ``"Gaseous"`` is a
constant and ``"Rain"`` a proposition, each distinct from the bare word of the same
letters.

``Atom.to_prover9()`` with no arguments and ``Constant.to_prover9()`` therefore write
such a name in quotes (a lower-case name stays bare, a name that cannot be quoted
keeps the refusal), and the kit's own reader reads the quoted symbol back.

What is pinned here:

* the exact text of the single-node renderers, derived by hand from that rule;
* the reader: a quoted symbol is a nullary atom in formula position, a constant in
  term position, never a variable; with arguments an atom / a function; a quoted
  name the writer cannot have produced is refused by name;
* the file scanner skips a quoted symbol whole;
* the round trip ``parse_prover9(node.to_prover9()) == node`` over thousands of
  random formulas whose names are upper-case, underscore-initial, keyword-like
  (``all``, ``exists``, ``v``) and lower-case;
* against the REAL Prover9, where there is one (the live tests skip, with a reason,
  where there is none): Prover9's verdict on the text the single-node renderers write
  equals Z3's verdict on the nodes, and the same problems written with the bare
  words are misread or refused (the control: it shows the comparison has the power to
  see the defect).
"""

import random
import re
import string

import pytest

from unicode_fol_kit import is_valid
from unicode_fol_kit.atp import prover9_entailment as p9
from unicode_fol_kit.atp.prover9_entailment import Prover9Rejected
from unicode_fol_kit.atp.protocol import Prover9Backend
from unicode_fol_kit.fol._msfl_nodes import SortedConstant
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Iff, Implies, Not, Or, Quantifier, Variable,
)
from unicode_fol_kit.fol.prover9_input import (
    Prover9ParsingError, parse_prover9, parse_prover9_problem,
)


def N(name):
    """A proposition: an atom with no arguments."""
    return Atom(name, [])


def P(*args):
    return Atom("P", list(args))


# --------------------------------------------------------------------------- #
# The single-node renderers (hand-derived from the rule in the module docstring).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name, text", [
    # Upper-case initial: a variable to Prover9 when bare, so quoted.
    ("Rain", '"Rain"'), ("R", '"R"'), ("Wet2", '"Wet2"'), ("RAIN", '"RAIN"'),
    # Underscore initial: a variable to this kit's reader and to the Prolog
    # convention (Prover9 itself reads it as a constant), so quoted too.
    ("_p", '"_p"'), ("__q1", '"__q1"'),
    # Keyword-like words: the capitalised ones are variables like any other upper-case word;
    # `v` is read as a plain symbol; `all` and `exists` are LADR's quantifier words, which it
    # reads as a quantifier wherever the symbol stands first and has a variable for an argument
    # ("exists(X) & ..." is `exists X` and a stray "&", measured on Prover9 2026-8A), so they
    # are written in double quotes, which are never a keyword.
    ("Exists", '"Exists"'), ("All", '"All"'), ("V", '"V"'),
    ("all", '"all"'), ("exists", '"exists"'), ("v", "v"),
    # Lower-case initial: a proposition as it is.
    ("rain", "rain"), ("wet2", "wet2"), ("c_Liquid", "c_Liquid"),
])
def test_a_nullary_atom_is_quoted_exactly_when_the_bare_word_is_a_variable(name, text):
    assert N(name).to_prover9() == text
    # In a compound the same text appears, nothing else changes.
    assert And(N(name), N("q")).to_prover9() == f"({text} & q)"
    assert Not(N(name)).to_prover9() == f"-({text})"


@pytest.mark.parametrize("name, text", [
    ("Gaseous", '"Gaseous"'), ("X", '"X"'), ("A1", '"A1"'), ("_x", '"_x"'), ("__y", '"__y"'),
    ("GASEOUS", '"GASEOUS"'), ("All", '"All"'),
    ("gaseous", "gaseous"), ("c", "c"), ("x", "x"), ("c_Liquid", "c_Liquid"),
    ("all", '"all"'), ("exists", '"exists"'), ("v", "v"),         # the quantifier words are quoted
    # Non-ASCII names are transliterated to a lower-case token first (theta, u015a, u0398)...
    ("θ", "theta"), ("Ś", "u015a"), ("Θ", "u0398"),
    # ... and a digit-leading name is not a variable.
    ("2008SummerOlympics", "2008SummerOlympics"),
])
def test_a_constant_is_quoted_exactly_when_the_bare_word_is_a_variable(name, text):
    assert Constant(name).to_prover9() == text
    assert P(Constant(name)).to_prover9() == f"P({text})"
    assert SortedConstant(name, "S").to_prover9() == text
    assert Atom("=", [Constant(name), Constant("c")]).to_prover9() == f"({text} = c)"
    assert P(Function("f", [Constant(name)])).to_prover9() == f"P(f({text}))"


def test_a_predicate_and_a_function_with_arguments_are_not_quoted():
    # The symbol is not an arity-0 term: Prover9 reads Human(X) as an atom and
    # Mother(Eve) as a function term even under prolog_style_variables, so only the
    # arity-0 argument Eve is read as a variable and only it is quoted.
    node = Atom("Human", [Function("Mother", [Constant("Eve")]), Variable("x")])
    assert node.to_prover9() == 'Human(Mother("Eve"), X)'
    assert Atom("Rain", [Variable("x")]).to_prover9() == "Rain(X)"


def test_the_defined_propositions_and_infix_atoms_are_unchanged():
    assert Atom("$true", []).to_prover9() == "$T"
    assert Atom("$false", []).to_prover9() == "$F"
    assert Atom("=", [Variable("x"), Constant("Y")]).to_prover9() == '(X = "Y")'
    assert Atom("≠", [Constant("A"), Constant("b")]).to_prover9() == '("A" != b)'


@pytest.mark.parametrize("name", ['A"b', "A b", "A.b", "A-b", "_x y", "A\nb"])
def test_a_constant_that_would_be_a_variable_and_cannot_be_quoted_is_still_refused(name):
    # LADR has no escape inside quotes, so these names cannot be written; bare they
    # would be read as a variable (or as several symbols). The refusal names the
    # constant, says why, and points at the problem writer.
    with pytest.raises(NotImplementedError) as excinfo:
        Constant(name).to_prover9()
    message = str(excinfo.value)
    assert repr(name) in message
    assert "VARIABLE" in message and "double quotes" in message
    assert "generate_prover9_input_with_mapping" in message


# --------------------------------------------------------------------------- #
# The reader.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text, expected", [
    ('"Rain"', N("Rain")),
    ('"Rain" -> "Wet"', Implies(N("Rain"), N("Wet"))),
    ('P("Gaseous")', P(Constant("Gaseous"))),
    ('P("_x")', P(Constant("_x"))),
    ('P(Mother("Eve"))', P(Function("Mother", [Constant("Eve")]))),
    ('("A" = b)', Atom("=", [Constant("A"), Constant("b")])),
    # A quoted name applied to arguments: an atom in formula position, a function in term position.
    ('"Foo"(a)', Atom("Foo", [Constant("a")])),
    ('P("f"(a))', P(Function("f", [Constant("a")]))),
    # A keyword-like word is a plain symbol.
    ('P(all, exists, v)', P(Constant("all"), Constant("exists"), Constant("v"))),
    # The comment character and the full stop after a quoted symbol are what they always were.
    ('"Rain" % a comment', N("Rain")),
    ('"Rain".', N("Rain")),
])
def test_the_reader_reads_a_quoted_symbol_as_a_name_that_is_never_a_variable(text, expected):
    assert parse_prover9(text) == expected


def test_a_quoted_and_a_bare_upper_case_word_are_read_differently():
    # Bare: a variable in term position (Prover9's reading under prolog_style_variables).
    assert parse_prover9("P(Gaseous)") == P(Variable("gaseous"))
    # Quoted: the constant.
    assert parse_prover9('P("Gaseous")') == P(Constant("Gaseous"))
    # The lenient bare reading of an upper-case proposition stays (Prover9 refuses it).
    assert parse_prover9("Rain") == N("Rain")


@pytest.mark.parametrize("text", ['P("a b")', 'P("a.b")', 'P("a%b")', 'P("")', 'P("2008x")',
                                  'P("f(x), y")', 'P("é")', 'P("a-b")'])
def test_a_quoted_name_the_writer_cannot_have_produced_is_refused_by_name(text):
    # Prover9 reads all of these (any text but a double quote may stand in quotes),
    # but the node built from them could not be written back as the same symbol, so
    # the reader refuses the symbol instead of building a node that changes meaning.
    with pytest.raises(Prover9ParsingError) as excinfo:
        parse_prover9(text)
    assert "quoted symbol" in str(excinfo.value)
    assert re.search(r'"[^"]*"', text).group(0) in str(excinfo.value)     # it names the symbol


def test_an_unterminated_quote_is_a_parse_error():
    with pytest.raises(Prover9ParsingError):
        parse_prover9('P("Gaseous)')


# --------------------------------------------------------------------------- #
# The file scanner.
# --------------------------------------------------------------------------- #

_FILE = '''set(prolog_style_variables).
% a "comment" with a quote and a full stop.
formulas(assumptions).
  P("Gaseous").            % a tail after a quoted symbol, with "a quote"
  "Rain" -> Q("Wet").
  (all X (Human(X) -> P(X, "Eve"))).
end_of_list.
formulas(goals).
  P(c).
end_of_list.
'''


def test_a_problem_file_with_quoted_symbols_and_comments_is_read():
    records = parse_prover9_problem(_FILE)
    assert [(r.role, r.formula) for r in records] == [
        ("assumptions", P(Constant("Gaseous"))),
        ("assumptions", Implies(N("Rain"), Atom("Q", [Constant("Wet")]))),
        ("assumptions", Quantifier("∀", Variable("x"), Implies(
            Atom("Human", [Variable("x")]), Atom("P", [Variable("x"), Constant("Eve")])))),
        ("goals", P(Constant("c"))),
    ]


@pytest.mark.parametrize("name", ["a.b", "a%b", "a. b"])
def test_a_dot_or_a_percent_inside_a_quoted_symbol_ends_no_statement_and_starts_no_comment(name):
    # Prover9 reads quoted text raw, so `P("a.b").` is ONE statement. The scanner
    # must not cut it at the '.' (the old scanner did: it handed the reader `P("a`),
    # nor strip a '%' as a comment; it reaches the reader whole, which then refuses the
    # name by name -- the message quotes the whole symbol, not a fragment of it.
    text = f'formulas(assumptions).\n  P("{name}").\nend_of_list.\n'
    with pytest.raises(Prover9ParsingError) as excinfo:
        parse_prover9_problem(text)
    assert f'"{name}"' in str(excinfo.value)
    assert "unterminated" not in str(excinfo.value)


def test_a_quote_that_is_not_closed_is_refused_not_skipped():
    for text in ['formulas(assumptions).\n  P("x.\nend_of_list.\n',
                 'formulas(assumptions).\n  P(a). % "\n  Q("b.\nend_of_list.\n']:
        with pytest.raises(Prover9ParsingError):
            parse_prover9_problem(text)


def test_a_comment_hides_a_quote_and_a_quote_hides_a_comment():
    # A '"' inside a % comment opens no quoted symbol, and a '%' inside a quoted
    # symbol opens no comment (the symbol is then refused by name, see above).
    records = parse_prover9_problem('% it\'s a "quoted\nP("Gaseous").\n')
    assert [r.formula for r in records] == [P(Constant("Gaseous"))]


# --------------------------------------------------------------------------- #
# The round trip, over random formulas.
# --------------------------------------------------------------------------- #

_CONSTANTS = ["a", "b", "gaseous", "Gaseous", "GASEOUS", "X", "A1", "_x", "__y", "Person",
              "person", "c_Liquid", "all", "exists", "v", "All", "Exists", "V"]
_PREDICATES = ["P", "Q", "Human", "Pers", "Rain"]
_FUNCTIONS = ["f", "Mother", "g", "Fn", "v"]
_PROPOSITIONS = ["Rain", "rain", "Wet", "_p", "Zed", "all", "exists", "v", "All", "Exists", "V"]


def _term(rng, depth, variables):
    roll = rng.random()
    if variables and roll < 0.2:
        return rng.choice(variables)
    if depth > 0 and roll < 0.5:
        return Function(rng.choice(_FUNCTIONS),
                        [_term(rng, depth - 1, variables) for _ in range(rng.randint(1, 2))])
    return Constant(rng.choice(_CONSTANTS))


def _formula(rng, depth, variables):
    roll = rng.random()
    if depth == 0 or roll < 0.35:
        if rng.random() < 0.15:
            return Atom("=", [_term(rng, 1, variables), _term(rng, 1, variables)])
        if rng.random() < 0.2:
            return N(rng.choice(_PROPOSITIONS))
        return Atom(rng.choice(_PREDICATES),
                    [_term(rng, 1, variables) for _ in range(rng.randint(1, 3))])
    if roll < 0.5:
        return Not(_formula(rng, depth - 1, variables))
    if roll < 0.85:
        connective = rng.choice((And, Or, Implies, Iff))
        return connective(_formula(rng, depth - 1, variables), _formula(rng, depth - 1, variables))
    variable = Variable(rng.choice("xyz"))
    return Quantifier(rng.choice("∀∃"), variable,
                      _formula(rng, depth - 1, variables + [variable]))


def _re_binds_a_name(node, enclosing=frozenset()):
    """Whether a binder of the formula sits inside the scope of a binder of the same name."""
    if isinstance(node, Quantifier):
        if node.variable.name in enclosing:
            return True
        enclosing = enclosing | {node.variable.name}
    return any(_re_binds_a_name(child, enclosing) for child in node._child_nodes())


def _bound_names_by_depth(node, scope=()):
    """``node`` with every bound variable named by the depth of its binder: two formulas that differ only in
    the names of their bound variables have one such form."""
    if isinstance(node, Quantifier):
        name = f"#{len(scope)}"
        return Quantifier(node.type, Variable(name),
                          _bound_names_by_depth(node.formula, scope + ((node.variable.name, name),)))
    if isinstance(node, Variable):
        for original, bound in reversed(scope):
            if original == node.name:
                return Variable(bound)
        return node
    return node.map_children(lambda child: _bound_names_by_depth(child, scope))


def _same_formula(read, original):
    """Equal, or equal up to the names of the bound variables when the formula re-binds a name: the text of
    such a formula is written under a fresh variable for the inner binder, so that Prover9 renames nothing."""
    if _re_binds_a_name(original):
        return _bound_names_by_depth(read) == _bound_names_by_depth(original)
    return read == original


def test_what_a_single_node_writes_the_reader_reads_back_as_the_same_node():
    rng = random.Random(20261004)
    keywords = {"all", "exists", "v"}
    quotes = bare_keywords = props = 0
    for index in range(2500):
        node = _formula(rng, 3, [])
        text = node.to_prover9()
        assert _same_formula(parse_prover9(text), node), text
        if index % 10 == 0:
            # The same node inside a whole file, after a comment. The text of a node is written
            # for ``set(prolog_style_variables)``, as every file of the writer sets it: without
            # the flag Prover9 reads a bare ``v`` (a constant here) as a variable.
            file_text = f"set(prolog_style_variables).\n% c \"q\"\nformulas(assumptions).\n  {text}.\nend_of_list.\n"
            (read,) = [r.formula for r in parse_prover9_problem(file_text)]
            assert _same_formula(read, node), file_text
        quotes += text.count('"')
        bare_keywords += any(
            (isinstance(n, Constant) and n.name in keywords)
            or (isinstance(n, Atom) and not n.args and n.predicate in keywords)
            for n in node.walk())
        props += any(isinstance(n, Atom) and not n.args and n.predicate not in Atom.INFIX_PREDS_P9
                     for n in node.walk())
    # The generator really exercises quoting, bare keyword-like words and propositions.
    assert quotes > 2500 and bare_keywords > 100 and props > 600


def test_the_round_trip_covers_a_name_in_every_role():
    # One symbol as a constant, a proposition, a predicate and a function in one
    # formula: four roles, and the quoted one is distinct from the bare one in each.
    node = And(And(N("Rain"), Atom("Rain", [Constant("Rain")])),
               Atom("=", [Function("Rain", [Constant("a")]), Constant("Rain")]))
    assert node.to_prover9() == '(("Rain" & Rain("Rain")) & (Rain(a) = "Rain"))'
    assert parse_prover9(node.to_prover9()) == node


# --------------------------------------------------------------------------- #
# The real binary, when there is one: Prover9's verdict on the single-node text
# against Z3's verdict on the nodes.
# --------------------------------------------------------------------------- #

_BINARY = Prover9Backend._binary()
_WSL = Prover9Backend._uses_wsl()
live = pytest.mark.skipif(
    not _BINARY,
    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or "
           "put 'prover9' on PATH; the text-level tests above carry the claim")


def _problem(premise_text, goal_text):
    """A Prover9 file whose two formulas are exactly the given single-node texts."""
    return ("set(prolog_style_variables).\n"
            "formulas(assumptions).\n"
            f"  {premise_text}.\n"
            "end_of_list.\n"
            "formulas(goals).\n"
            f"  {goal_text}.\n"
            "end_of_list.\n")


def _prover9_proves(premise_text, goal_text):
    """True / False, or the Prover9Rejected that says Prover9 refused to read the file."""
    try:
        return p9._run_prover9(_problem(premise_text, goal_text), _BINARY, timeout=60,
                               raise_on_rejection=True, use_wsl=_WSL)
    except Prover9Rejected as refusal:
        return refusal


@live
def test_live_prover9_reads_the_quoted_text_as_the_formula_says():
    # Hand-derived. P("Gaseous") entails itself and does NOT entail P(c) (two
    # different constants: interpret P as {Gaseous}); "Rain" -> "Wet" and "Rain"
    # entail "Wet" (modus ponens) but "Rain" alone does not entail "Wet".
    assert _prover9_proves('P("Gaseous")', 'P("Gaseous")') is True
    assert _prover9_proves('P("Gaseous")', "P(c)") is False
    assert _prover9_proves('(("Rain" -> "Wet") & "Rain")', '"Wet"') is True
    assert _prover9_proves('"Rain"', '"Wet"') is False
    # The bare spelling is what the quoting is for: P(Gaseous) is "for all X, P(X)".
    assert _prover9_proves("P(Gaseous)", "P(c)") is True


# Fixed arities, so the two texts of a pair never use one symbol with two arities
# (Prover9 refuses that), and no name is both a proposition and a constant.
_ARITY = {"P": 1, "Q": 2, "Human": 1, "Pers": 3}
_FUNCTION_ARITY = {"f": 1, "Mother": 1, "g": 2}
_DCONSTANTS = ["a", "b", "gaseous", "Gaseous", "GASEOUS", "X", "A1", "_x", "__y", "Person", "person",
               "c_Liquid", "all", "v", "exists"]
_DPROPOSITIONS = ["Rain", "rain", "Wet", "_p", "Zed"]


def _dterm(rng, depth, variables):
    roll = rng.random()
    if variables and roll < 0.2:
        return rng.choice(variables)
    if depth > 0 and roll < 0.5:
        name = rng.choice(list(_FUNCTION_ARITY))
        return Function(name, [_dterm(rng, depth - 1, variables)
                               for _ in range(_FUNCTION_ARITY[name])])
    return Constant(rng.choice(_DCONSTANTS))


def _dformula(rng, depth, variables):
    roll = rng.random()
    if depth == 0 or roll < 0.35:
        if rng.random() < 0.15:
            return Atom("=", [_dterm(rng, 1, variables), _dterm(rng, 1, variables)])
        if rng.random() < 0.25:
            return N(rng.choice(_DPROPOSITIONS))
        name = rng.choice(list(_ARITY))
        return Atom(name, [_dterm(rng, 1, variables) for _ in range(_ARITY[name])])
    if roll < 0.5:
        return Not(_dformula(rng, depth - 1, variables))
    if roll < 0.8:
        connective = rng.choice((And, Or, Implies, Iff))
        return connective(_dformula(rng, depth - 1, variables), _dformula(rng, depth - 1, variables))
    variable = Variable(rng.choice("xyz"))
    return Quantifier(rng.choice("∀∃"), variable,
                      _dformula(rng, depth - 1, variables + [variable]))


def _swap(node, old, new):
    """``node`` with the constant (or the proposition) ``old`` replaced by ``new``."""
    if isinstance(node, Constant):
        return Constant(new) if node.name == old else node
    if isinstance(node, Variable):
        return node
    if isinstance(node, Atom) and not node.args and node.predicate == old:
        return Atom(new, [])
    return node.map_children(lambda child: _swap(child, old, new))


def _problems(count, seed):
    """``count`` (premise, goal) pairs. The goal is the premise with one symbol replaced
    by its other-case twin (``Person`` for ``person``), or the premise itself: the pairs
    on which a reading of an upper-case word as a variable proves something false."""
    rng = random.Random(seed)
    pairs = []
    while len(pairs) < count:
        premise = _dformula(rng, 2, [])
        constants = [n.name for n in premise.walk() if isinstance(n, Constant)]
        propositions = [n.predicate for n in premise.walk()
                        if isinstance(n, Atom) and not n.args and n.predicate not in Atom.INFIX_PREDS_P9]
        goal = premise
        if constants and rng.random() < 0.7:
            old = rng.choice(constants)
            new = old.lower() if old != old.lower() else old.capitalize()
            # The twin must be a fresh constant: not a predicate or function name, and not the
            # name of a bound variable (Z3 reads the constant x and the variable x as one symbol,
            # Prover9 reads the constant `x` and the variable `X` as two).
            if new in _ARITY or new in _FUNCTION_ARITY or new in ("x", "y", "z"):
                new = "zz"
            goal = _swap(premise, old, new)
        elif propositions:
            old = rng.choice(propositions)
            goal = _swap(premise, old, old.lower() if old != old.lower() else "Zq")
        try:
            valid = is_valid(Implies(premise, goal))
        except Exception:                       # a problem Z3 cannot settle is not a data point
            continue
        pairs.append((premise, goal, valid))
    return pairs


def _bare(text):
    """The text a renderer without the quoting would write: the same words, unquoted."""
    return re.sub(r'"([A-Za-z_][A-Za-z0-9_]*)"', r"\1", text)


def _compare(pairs, render):
    tally = {"agree": 0, "misread": 0, "refused": 0, "missed": 0}
    for premise, goal, valid in pairs:
        answer = _prover9_proves(render(premise.to_prover9()), render(goal.to_prover9()))
        if isinstance(answer, Prover9Rejected):
            tally["refused"] += 1
        elif answer == valid:
            tally["agree"] += 1
        elif answer:
            tally["misread"] += 1           # Prover9 proved what Z3 calls invalid
        else:
            tally["missed"] += 1            # Prover9 found no proof of a valid goal
    return tally


@live
def test_live_prover9_answers_as_z3_does_on_the_text_the_single_node_renderers_write():
    pairs = _problems(250, seed=4242)
    assert sum(1 for *_, valid in pairs if valid) >= 50           # the corpus has valid goals...
    assert sum(1 for *_, valid in pairs if not valid) >= 50       # ... and invalid ones
    tally = _compare(pairs, lambda text: text)
    # Every text is read as the formula says: Prover9 proves exactly what Z3 calls valid.
    assert tally == {"agree": 250, "misread": 0, "refused": 0, "missed": 0}, tally


@live
def test_live_control_the_same_problems_with_the_bare_words_are_misread_or_refused():
    pairs = _problems(100, seed=777)
    tally = _compare(pairs, _bare)
    # The control shows the comparison above can see the defect: written with the bare
    # words (the text Atom.to_prover9 wrote before the quoting, and what Constant.to_prover9
    # would write without its refusal) Prover9 proves goals Z3 calls invalid (an upper-case
    # word is a variable, so P(Person) is "for all X, P(X)") and refuses the files in which
    # an upper-case proposition stands bare. Measured on this corpus with Prover9 2026-8A:
    # 26 misreads, 24 refusals and 50 agreements out of 100; the bounds are lower, so they
    # hold for another corpus-sized sample of another Prover9 build.
    assert tally["misread"] >= 10, tally
    assert tally["refused"] >= 10, tally
    assert tally["agree"] < 100
