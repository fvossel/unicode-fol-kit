r"""Words that LADR, or a reader of its files, takes for syntax: ``if`` with three arguments, ``end_of_list``,
``formulas``.

Measured on Prover9 2026-8A, with a sweep over the words of LADR's source (the commands ``set``,
``clear``, ``assign``, ``op``, ``redeclare``, ``lex``, ``skolem``, ``formulas``, ``clauses``, ``terms``,
``list``, ``if``, ``end_if``, ``end_of_list``, the operator words ``all``, ``exists``, ``v``, the words of the
operator table and the names of the symbols ``true`` and ``false``), each as a proposition, a constant and a
predicate and a function of one to four arguments, with a variable and with constants as arguments:

* ``if`` with THREE arguments: LADR reads the first argument as a formula. ``(all W if(W, a, a))`` is
  refused ("cannot be used as atomic formulas, because they are variables: W"), and ``if(a, b, c)`` makes
  ``a`` a relation symbol, which a constant ``a`` of the file contradicts. At any other number of
  arguments ``if`` is an ordinary symbol.
* ``end_of_list`` with no argument: inside a list the bare word ends it ("Unrecognized command or
  list"). As an argument it is an ordinary constant.
* ``formulas`` with one argument: Prover9 reads ``formulas(alpha)`` in a list as an atom, but it is also
  the header of a list, and a reader of the file cannot tell them apart.
* every other word of the sweep reads as an ordinary symbol in every position (``v`` is echoed infix, as
  the same symbol).

A double-quoted symbol is a symbol of its own, never one of these. A single renderer
(``Node.to_prover9``) writes them quoted, and the problem writer gives them a token of their own.
"""

import pytest

from unicode_fol_kit.atp.prover9_entailment import generate_prover9_input_with_mapping
from unicode_fol_kit.atp.protocol import Prover9Backend, get_backend
from unicode_fol_kit.fol.nodes import Atom, Constant, Function, Quantifier, Variable
from unicode_fol_kit.fol.prover9_input import Prover9ParsingError, parse_prover9, parse_prover9_problem

x, w = Variable("x"), Variable("w")
a, b, c, alpha = Constant("a"), Constant("b"), Constant("c"), Constant("alpha")


def _lines(text):
    lines = [line.strip() for line in text.splitlines()]
    assumptions = lines[lines.index("formulas(assumptions).") + 1:]
    assumptions = assumptions[:assumptions.index("end_of_list.")]
    goals = lines[lines.index("formulas(goals).") + 1:]
    goals = goals[:goals.index("end_of_list.")]
    return assumptions, goals


# --- the single renderers --------------------------------------------------- #

@pytest.mark.parametrize("node, text", [
    (Atom("if", [a, b, c]), '"if"(a, b, c)'),
    (Function("if", [a, b, c]), '"if"(a, b, c)'),
    (Atom("end_of_list", []), '"end_of_list"'),
    (Constant("end_of_list"), '"end_of_list"'),
    (Atom("formulas", [a]), '"formulas"(a)'),
    (Function("formulas", [a]), '"formulas"(a)'),
])
def test_a_single_renderer_writes_a_reserved_word_in_double_quotes(node, text):
    assert node.to_prover9() == text


@pytest.mark.parametrize("node, text", [
    (Atom("if", [a]), "if(a)"), (Atom("if", [a, b]), "if(a, b)"), (Atom("if", [a, b, c, a]), "if(a, b, c, a)"),
    (Atom("formulas", [a, b]), "formulas(a, b)"), (Atom("formulas", []), "formulas"),
    (Function("end_of_list", [a]), "end_of_list(a)"), (Atom("end_if", []), "end_if"),
    (Atom("clauses", [a]), "clauses(a)"), (Atom("set", [a]), "set(a)"),
])
def test_the_same_word_at_another_number_of_arguments_is_an_ordinary_symbol(node, text):
    assert node.to_prover9() == text


@pytest.mark.parametrize("node", [Atom("if", [a, b, c]), Atom("end_of_list", []), Atom("formulas", [a]),
                                  Atom("P", [Function("if", [a, b, c])]), Atom("P", [Constant("end_of_list")])])
def test_the_reader_reads_the_quoted_form_back_as_the_node(node):
    assert parse_prover9(node.to_prover9()) == node


# --- the problem writer ------------------------------------------------------ #

def test_the_writer_gives_a_reserved_word_a_token_of_its_own():
    premises = [Atom("if", [a, b, c]), Atom("end_of_list", []), Atom("formulas", [a])]
    text, names = generate_prover9_input_with_mapping(premises, Atom("end_of_list", []))
    assumptions, goals = _lines(text)
    assert names.symbols[("predicate", "if", 3)] != "if"
    assert names.symbols[("predicate", "end_of_list", 0)] != "end_of_list"
    assert names.symbols[("predicate", "formulas", 1)] != "formulas"
    # The only statements that are the bare word are the two ends of the lists.
    assert [ln for ln in text.splitlines() if ln.strip() in ("end_of_list.", "end_of_list")] == ["end_of_list."] * 2
    assert goals == [f"{names.symbols[('predicate', 'end_of_list', 0)]}."]


def test_a_word_reserved_at_one_arity_keeps_its_spelling_at_another():
    premises = [Atom("if", [a, b]), Atom("if", [a, b, c]), Atom("formulas", [a, b]), Atom("formulas", [a])]
    _, names = generate_prover9_input_with_mapping(premises, Atom("G", []))
    assert names.symbols[("predicate", "if", 2)] == "if"
    assert names.symbols[("predicate", "formulas", 2)] == "formulas"
    assert names.symbols[("predicate", "if", 3)] not in ("if",)
    tokens = list(names.symbols.values())
    assert len(set(tokens)) == len(tokens)


def test_the_token_of_a_reserved_word_is_not_another_symbols_spelling():
    premises = [Atom("if2", [a]), Atom("if", [a, b, c]), Atom("if3", [a])]
    _, names = generate_prover9_input_with_mapping(premises, Atom("G", []))
    tokens = list(names.symbols.values())
    assert len(set(tokens)) == len(tokens) and names.symbols[("predicate", "if", 3)] not in ("if", "if2", "if3")


def test_the_reader_reads_the_text_the_writer_writes_for_formulas_as_a_predicate():
    # The text of formulas(alpha) ⊢ formulas(alpha) was refused by the reader as a nested list header.
    text, names = generate_prover9_input_with_mapping([Atom("formulas", [alpha])], Atom("formulas", [alpha]))
    token = names.symbols[("predicate", "formulas", 1)]
    read = parse_prover9_problem(text)
    assert [(r.role, r.formula) for r in read] == [("assumptions", Atom(token, [alpha])),
                                                   ("goals", Atom(token, [alpha]))]


def test_the_reader_still_refuses_a_list_header_inside_an_open_list():
    # A file that forgot an end_of_list is not read as if `formulas(goals)` were an atom.
    with pytest.raises(Prover9ParsingError) as refused:
        parse_prover9_problem("formulas(assumptions).\n P(a).\nformulas(goals).\n Q(a).\nend_of_list.\n")
    assert "nested" in str(refused.value)


# --- against the real Prover9 ----------------------------------------------- #

_BINARY = Prover9Backend._binary()
live = pytest.mark.skipif(
    _BINARY is None,
    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or "
           "put 'prover9' on PATH; the text-level tests above carry the claim")


def _decide(goal, premises):
    return get_backend("prover9").decide(goal, premises, timeout=30000)


def P(*args):
    return Atom("P", list(args))


_PROBLEMS = [
    ("if with a variable first argument",
     [Quantifier("∀", x, Atom("if", [x, alpha, alpha]))], Atom("if", [alpha, alpha, alpha]), "valid",
     "the instance x = alpha"),
    ("if as a function with a variable first argument",
     [Quantifier("∀", x, P(Function("if", [x, alpha, alpha])))], P(Function("if", [alpha, alpha, alpha])), "valid",
     "the instance x = alpha"),
    ("if with constants that are also terms elsewhere",
     [Atom("if", [a, b, c]), P(a)], Quantifier("∃", x, Atom("if", [x, b, c])), "valid", "witness a"),
    ("if is no conditional: if(a, b, c) and a do not give b",
     [Atom("if", [a, b, c]), Atom("A", [a])], Atom("B", [b]), "invalid",
     "if/3 is an uninterpreted predicate: U={0,1}, everything 0, A={0}, B={}"),
    ("end_of_list as a proposition", [Atom("end_of_list", [])], Atom("end_of_list", []), "valid", "the premise"),
    ("end_of_list as a proposition is not provable alone", [], Atom("end_of_list", []), "invalid",
     "the proposition is false in a structure that makes it false"),
    ("end_of_list as a constant", [P(Constant("end_of_list"))], P(Constant("end_of_list")), "valid", "the premise"),
    ("formulas as a predicate", [Atom("formulas", [alpha])], Atom("formulas", [alpha]), "valid", "the premise"),
    ("formulas is no list header", [Atom("formulas", [alpha])], Atom("formulas", [a]), "invalid",
     "U={0,1}, formulas={0}, alpha=0, a=1"),
]


@live
@pytest.mark.parametrize("name, premises, goal, verdict, reason", _PROBLEMS, ids=[p[0] for p in _PROBLEMS])
def test_live_prover9_reads_a_reserved_word_as_the_symbol_it_is(name, premises, goal, verdict, reason):
    result = _decide(goal, premises)
    if verdict == "valid":
        assert result.status == "proved", (name, reason, result)
    else:
        assert (result.status, result.reason) == ("unknown", "incomplete"), (name, reason, result)


@live
def test_live_prover9_reads_a_single_renderers_quoted_word_as_a_symbol_of_its_own():
    # "if"(a, b, c) is a symbol with its quotes, no conditional: the file is read and a plain proof is found.
    import os
    from unicode_fol_kit.atp.prover9_entailment import _run_prover9
    text = "\n".join([
        "set(prolog_style_variables).",
        "formulas(assumptions).",
        '  (all X "if"(X, a, a)).',
        "end_of_list.",
        "formulas(goals).",
        '  "if"(a, a, a).',
        "end_of_list.",
        ""])
    assert _run_prover9(text, _BINARY, timeout=30, raise_on_rejection=True,
                        use_wsl=os.environ.get("UFK_PROVER9_WSL") == "1")
