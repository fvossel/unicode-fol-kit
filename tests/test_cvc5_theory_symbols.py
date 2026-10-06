"""A symbol of this kit named like a symbol of an SMT-LIB theory is renamed, under every logic, and never a crash.

cvc5 knows hundreds of names under the logic ``ALL`` (``+``, ``<``, ``select``, ``str.len``, ``fp.add``,
``set.union``, ...) and refuses ``declare-fun`` of one of them: a parse error for a predicate, and for a
function or a constant a native access violation that ends the Python process (measured on cvc5 1.3.4: 231
of 343 candidate names, each in a child process). This kit reads such a name as an ordinary UNINTERPRETED
symbol over its one sort, which is what ``to_z3`` declares and what Z3 accepts. Renaming the nine Core symbols
alone would be enough only under the default logic ``UF``; a caller who passes ``logic="ALL"`` (or
``to_smtlib``, whose default logic is ``ALL``) needs every theory's names renamed as well.

``cvc5_backend._SMTLIB_THEORIES`` is the table of the names: every symbol of the standard theories (Core,
Ints, Reals, Reals_Ints, ArraysEx, FixedSizeBitVectors, FloatingPoint, Strings) and the further names cvc5
knows. Each name of it is run through cvc5 under ``ALL``, as a predicate, a function and a constant, in a
CHILD process, so that a regression is a failed assertion about an exit code and not the death of the test
run. The other names that ended the process or were refused (a name that begins with ``.`` or ``@``, one
that is ``-1``, one with ``|``, ``\\`` or ``'`` in it, the reserved word ``par``) are run the same way,
under ``UF`` too.

Hand-derived expectations, whatever the name ``s`` is called, because it is uninterpreted:

* predicate: ``∀x (P(x) → s(x, cb)) ⊢ P(ca) → s(ca, cb)`` is VALID (one instantiation) and
  ``P(ca) ⊬ s(ca, cb)`` is NOT (two elements, ``P = {ca}``, ``s`` empty);
* function: ``∀x P(s(x, cb)) ⊢ P(s(ca, cb))`` is VALID and ``P(ca) ⊬ P(s(ca, cb))`` is NOT;
* constant: ``P(s) ⊢ P(s)`` is VALID and ``P(ca) ⊬ P(s)`` is NOT.
"""
import json
import subprocess
import sys

import pytest

pytest.importorskip("cvc5")

import z3

from unicode_fol_kit.atp.cvc5_backend import (
    _SMTLIB_CORE_SYMBOLS, _SMTLIB_RESERVED_WORDS, _SMTLIB_THEORIES, _SMTLIB_THEORY_SYMBOLS,
    _is_smtlib_safe, _sanitize_many_for_smtlib,
)
from unicode_fol_kit.atp.z3_input import to_smtlib
from unicode_fol_kit.fol.nodes import Atom, Constant, Function, Implies, Quantifier, Variable

CA, CB, X = Constant("ca"), Constant("cb"), Variable("x")


def P(term):
    return Atom("P", [term])


def problems(name, role):
    """``(entailed, not_entailed)`` as ``(premises, goal)``: the hand-derived problems of the module docstring."""
    if role == "predicate":
        entailed = ([Quantifier("∀", X, Implies(P(X), Atom(name, [X, CB])))], Implies(P(CA), Atom(name, [CA, CB])))
        not_entailed = ([P(CA)], Atom(name, [CA, CB]))
    elif role == "function":
        entailed = ([Quantifier("∀", X, P(Function(name, [X, CB])))], P(Function(name, [CA, CB])))
        not_entailed = ([P(CA)], P(Function(name, [CA, CB])))
    else:
        entailed = ([P(Constant(name))], P(Constant(name)))
        not_entailed = ([P(CA)], P(Constant(name)))
    return entailed, not_entailed


ROLES = ("predicate", "function", "constant")

_CHILD = r"""
import json, sys
from unicode_fol_kit.atp.cvc5_backend import Cvc5Backend
from unicode_fol_kit.fol.nodes import (Atom, Constant, Function, Implies, Quantifier, Variable)

names, logics = json.loads(sys.argv[1]), json.loads(sys.argv[2])
ca, cb, x = Constant("ca"), Constant("cb"), Variable("x")
P = lambda t: Atom("P", (t,))
out = []
for logic in logics:
    for name in names:
        for role in ("predicate", "function", "constant"):
            if role == "predicate":
                cases = (([Quantifier("∀", x, Implies(P(x), Atom(name, (x, cb))))], Implies(P(ca), Atom(name, (ca, cb)))),
                         ([P(ca)], Atom(name, (ca, cb))))
            elif role == "function":
                cases = (([Quantifier("∀", x, P(Function(name, (x, cb))))], P(Function(name, (ca, cb)))),
                         ([P(ca)], P(Function(name, (ca, cb)))))
            else:
                cases = (([P(Constant(name))], P(Constant(name))), ([P(ca)], P(Constant(name))))
            statuses = []
            keys = None
            for premises, goal in cases:
                verdict = Cvc5Backend().decide(goal, premises, timeout=10000, logic=logic)
                statuses.append(verdict.status)
                if verdict.countermodel:
                    keys = sorted(verdict.countermodel["assignment"])
            out.append({"logic": logic, "name": name, "role": role, "statuses": statuses, "keys": keys})
print(json.dumps(out))
"""


def run_child(source, *argv):
    done = subprocess.run([sys.executable, "-c", source, *argv], capture_output=True, text=True,
                          encoding="utf-8", timeout=1800)
    # 0, not 3221225477 (Windows access violation) or -11 (SIGSEGV)
    assert done.returncode == 0, (done.returncode, done.stderr[-600:])
    return json.loads(done.stdout.strip().splitlines()[-1])


def decide_names(names, logics):
    return run_child(_CHILD, json.dumps(list(names)), json.dumps(list(logics)))


# ---------------------------------------------------------------------------------------------
# the table
# ---------------------------------------------------------------------------------------------
#: A few symbols of each standard theory, written down from the SMT-LIB standard (not read off the table).
STANDARD = {
    "Core": ["true", "false", "not", "=>", "and", "or", "xor", "=", "distinct", "ite", "Bool"],
    "Ints": ["Int", "-", "+", "*", "div", "mod", "abs", "<=", "<", ">=", ">", "divisible"],
    "Reals": ["Real", "/"],
    "Reals_Ints": ["to_real", "to_int", "is_int"],
    "ArraysEx": ["Array", "select", "store"],
    "FixedSizeBitVectors": ["BitVec", "concat", "extract", "bvnot", "bvand", "bvadd", "bvmul", "bvudiv",
                            "bvshl", "bvult", "bvslt", "bvcomp", "zero_extend", "rotate_left", "bvsmod"],
    "FloatingPoint": ["Float32", "RoundingMode", "RNE", "roundTowardZero", "fp", "fp.add", "fp.isNaN",
                      "fp.to_real", "to_fp", "NaN", "+oo"],
    "Strings": ["String", "RegLan", "str.++", "str.len", "str.at", "str.in_re", "re.*", "re.union",
                "re.allchar", "str.to_int", "str.replace_all"],
}


@pytest.mark.parametrize("theory", sorted(STANDARD))
def test_the_table_holds_the_symbols_of_every_standard_theory(theory):
    missing = [name for name in STANDARD[theory] if name not in _SMTLIB_THEORY_SYMBOLS]
    assert missing == []


def test_the_core_symbols_and_the_reserved_words_are_unsafe_names_too():
    assert _SMTLIB_CORE_SYMBOLS <= _SMTLIB_THEORY_SYMBOLS
    for name in sorted(_SMTLIB_CORE_SYMBOLS | _SMTLIB_RESERVED_WORDS | _SMTLIB_THEORY_SYMBOLS):
        assert not _is_smtlib_safe(name), name


@pytest.mark.parametrize("name", ["Likes", "f", "cc", "x1", "świątek", "a b", "a:b", "#x1", "BINARY", "NUMERAL",
                                  "a-b", "+a", "plus", "Float", "string", "int"])
def test_an_ordinary_name_or_a_name_z3_quotes_correctly_is_left_alone(name):
    assert _is_smtlib_safe(name)


@pytest.mark.parametrize("name", ["2008x", "-1", "-0", "-1.5", ".5", "@a", "a|b", "a\\b", "a'b", "'a", "par",
                                  "let", "select", "+", "str.len", ""])
def test_these_names_are_not_safe(name):
    assert not _is_smtlib_safe(name)


@pytest.mark.parametrize("role", ROLES)
def test_every_name_of_the_table_is_renamed_to_a_distinct_safe_token_and_back(role):
    # a binary ``=`` atom is the native equality, which declares nothing and is not renamed
    names = sorted(name for name in _SMTLIB_THEORY_SYMBOLS if not (role == "predicate" and name == "="))

    def node(name):
        if role == "predicate":
            return Atom(name, [CA, CB])
        if role == "function":
            return P(Function(name, [CA, CB]))
        return P(Constant(name))

    sanitised, mapping = _sanitize_many_for_smtlib([node(name) for name in names])
    reverse = mapping.reverse()
    tokens = []
    for name, rewritten in zip(names, sanitised):
        token = rewritten.predicate if role == "predicate" else rewritten.args[0].name
        tokens.append(token)
        assert _is_smtlib_safe(token) and token not in _SMTLIB_THEORY_SYMBOLS, (name, token)
        assert reverse[token] == name
    assert len(set(tokens)) == len(names)


def test_the_logic_does_not_decide_what_is_renamed():
    # the sanitiser has no logic parameter at all: the renaming is the same under UF and under ALL
    sanitised, mapping = _sanitize_many_for_smtlib([P(Function("select", [CA, CB]))])
    assert mapping.symbol("function", "select", 2) != "select"
    assert sanitised[0].args[0].name != "select"


# ---------------------------------------------------------------------------------------------
# cvc5 under ALL, in a child process
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("theory", sorted(_SMTLIB_THEORIES))
def test_every_name_of_the_table_is_an_uninterpreted_symbol_to_cvc5_under_all(theory):
    results = decide_names(_SMTLIB_THEORIES[theory], ["ALL"])
    assert len(results) == len(_SMTLIB_THEORIES[theory]) * len(ROLES)
    for r in results:
        # entailed: proved.  not entailed: refuted (cvc5 may also give up on it, never prove it)
        assert r["statuses"][0] == "proved", r
        assert r["statuses"][1] in ("refuted", "unknown"), r


def test_the_countermodel_names_a_theory_symbol_by_its_own_name():
    results = decide_names(["+", "select", "str.len", "<="], ["ALL"])
    constants = [r for r in results if r["role"] == "constant"]
    assert [r["keys"] for r in constants] == [sorted(["P", "ca", name]) for name in ["+", "select", "str.len", "<="]]


# ---------------------------------------------------------------------------------------------
# the other names that ended the process or were refused, under the default logic and under ALL
# ---------------------------------------------------------------------------------------------
ODD = ["-1", "-0", "-1.5", ".5", ".a", "@a", "a|b", "a\\b", "a'b", "'a", "|", "par", "2008x", "let", "=",
       "true"]


def test_a_name_cvc5_reads_as_a_literal_or_a_reserved_word_or_cannot_read_back_is_renamed():
    results = decide_names(ODD, ["UF", "ALL"])
    assert len(results) == len(ODD) * len(ROLES) * 2
    for r in results:
        assert r["statuses"][0] == "proved", r
        assert r["statuses"][1] in ("refuted", "unknown"), r
    constants = [r for r in results if r["role"] == "constant" and r["statuses"][1] == "refuted"]
    # the countermodel of a constant reports the name as the problem wrote it, not the token
    assert constants and all(r["keys"] == sorted(["P", "ca", r["name"]]) for r in constants)


# ---------------------------------------------------------------------------------------------
# the text to_smtlib writes (its default logic is ALL), a variable, and a Measure
# ---------------------------------------------------------------------------------------------
_READ_TEXT = (
    "import sys, cvc5\n"
    "solver = cvc5.Solver()\n"
    "parser = cvc5.InputParser(solver)\n"
    "manager = parser.getSymbolManager()\n"
    "parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, sys.stdin.read(), 'text')\n"
    "while True:\n"
    "    command = parser.nextCommand()\n"
    "    if command.isNull():\n"
    "        break\n"
    "    if command.getCommandName() == 'check-sat':\n"
    "        continue\n"
    "    command.invoke(solver, manager)\n"
    "print('read')\n")


@pytest.mark.parametrize("name", ["+", "select", "str.len", "set.union", "fp.add", "<", "par", "-1", ".a"])
def test_cvc5_reads_the_text_to_smtlib_writes_for_a_theory_symbol(name):
    text = to_smtlib(Atom("P", [Function(name, [CA, CB])]), [Atom(name, [CA]), P(Constant(name))])
    assert text.startswith("(set-logic ALL)")
    z3.parse_smt2_string(text)                                  # Z3 reads it, and so does cvc5
    done = subprocess.run([sys.executable, "-c", _READ_TEXT], input=text, capture_output=True, text=True,
                          encoding="utf-8", timeout=300)
    assert done.returncode == 0 and "read" in done.stdout, (done.returncode, done.stderr[-400:])


_VARIABLE_CHILD = r"""
import json
from unicode_fol_kit.atp.cvc5_backend import Cvc5Backend
from unicode_fol_kit.fol.nodes import Atom, Constant, Measure, Quantifier, Variable

out = []
for name in ["select", "not", "2008x", "str.len", "-1"]:
    v = Variable(name)
    # ∀v P(v) ⊢ P(c): valid.  The variable is named like a theory symbol.
    out.append(Cvc5Backend().decide(Atom("P", [Constant("c")]), [Quantifier("∀", v, Atom("P", [v]))],
                                    timeout=10000, logic="ALL").status)
a, b = Constant("a"), Constant("b")
# the predicate measure(a, b) next to the term μ(a, b), which is the function measure(a, b): two symbols
out.append(Cvc5Backend().decide(Atom("P", [Measure(a, b)]),
                                [Atom("measure", [a, b]), Atom("P", [Measure(a, b)])], timeout=10000).status)
print(json.dumps(out))
"""


def test_a_variable_named_like_a_theory_symbol_and_a_measure_next_to_a_predicate_of_its_name():
    assert run_child(_VARIABLE_CHILD) == ["proved"] * 6
