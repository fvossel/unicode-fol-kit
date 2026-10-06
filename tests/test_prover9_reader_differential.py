r"""The Prover9 reader against two oracles it does not share code with.

**The writer's own text reads back.** Whatever :func:`generate_prover9_input_with_mapping` writes, the
reader reads as the same formulas, node for node: the same predicates, functions, constants, numerals and
connectives, with the bound variables compared up to their names (the text writes a variable in upper
case and the reader reads it in lower case, and a binder that Prover9 would rename is written under a
fresh name). An exclusive or is written as the conjunction ``(l | r) & -(l & r)``, as the writer documents,
so that is the form that is read. The names are drawn from a pool made of the awkward ones: words that
begin with ``all`` or ``exists``, ``formulas`` and ``end_of_list`` at several arities, names that begin
with a capital, with an underscore or with ``x`` and a digit, and constants spelled like the variables.
A problem the writer refuses by name is not read back.

**Z3 and the real Prover9 agree on the text.** Random Prover9 files in the grammar of the reader (both
variable conventions, quantifiers over lower- and upper-case names, ``<-``, predicates that begin with
``all`` and ``exists``) are decided by Z3 through the reader and by the real Prover9 on the text itself.
No variable that no quantifier binds occurs in them (Prover9 closes such a variable universally, the kit
reads one unknown element). A third of the files have a goal that is an alpha-variant of a premise or a
weakening of it, so they are valid by construction and the rest are mostly not: the two oracles must not
give opposite verdicts, and the number of each is checked so that the comparison is not one-sided.
"""

import os
import random
import subprocess
import tempfile

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import prover9_entailment as writer
from unicode_fol_kit.atp.protocol import Prover9Backend
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Contrast, Count, Function, Iff, Implies, Not, Number, Or, Quantifier, Variable, Xor,
)
from unicode_fol_kit.fol.prover9_input import parse_prover9_problem

# --------------------------------------------------------------------------- #
# The writer's text, read back.
# --------------------------------------------------------------------------- #

_PREDICATES = ["P", "Q", "R", "allowed", "exists_in", "all_men", "existsRoom", "Human", "formulas", "end_of_list",
               "set", "op", "v", "a", "X", "_p", "p1", "Xa", "if", "clear", "assign", "all", "exists", "x0", "u"]
_CONSTANTS = ["alpha", "a", "b", "Gaseous", "x0", "X", "_c", "all", "exists", "v", "u", "z", "w1", "Xa", "xa", "c1",
              "formulas", "end_of_list", "set", "op", "x", "y"]
_FUNCTIONS = ["f", "g", "F", "allf", "h2", "formulas", "set", "x1"]
_VARIABLES = ["x", "y", "z", "w", "X", "x0", "y1", "v", "u", "_y", "xa", "Xa", "all", "a"]
_NUMBERS = [0, 1, 2, -1, 2.5, 1.5, 10, 100]
_COMPARISONS = ["=", "≠", "<", "≤", ">", "≥"]


def _term(rng, scope, depth):
    roll = rng.random()
    if depth <= 0 or roll < 0.45:
        if scope and rng.random() < 0.6:
            return Variable(rng.choice(scope))
        if rng.random() < 0.12:
            return Variable(rng.choice(_VARIABLES))          # a free variable: the writer makes it a constant
        if rng.random() < 0.12:
            return Number(rng.choice(_NUMBERS))
        return Constant(rng.choice(_CONSTANTS))
    if roll < 0.8:
        return Function(rng.choice(_FUNCTIONS), [_term(rng, scope, depth - 1) for _ in range(rng.randint(1, 2))])
    operator = rng.choice(["+", "*", "/", "-"])
    if operator == "-" and rng.random() < 0.4:
        return Function("-", [_term(rng, scope, depth - 1)])
    return Function(operator, [_term(rng, scope, depth - 1), _term(rng, scope, depth - 1)])


def _formula(rng, scope, depth):
    roll = rng.random()
    if depth <= 0 or roll < 0.25:
        pick = rng.random()
        if pick < 0.15:
            return Atom(rng.choice(_COMPARISONS), [_term(rng, scope, 1), _term(rng, scope, 1)])
        if pick < 0.2:
            return Atom(rng.choice(["$true", "$false"]), [])
        return Atom(rng.choice(_PREDICATES), [_term(rng, scope, 1) for _ in range(rng.choice([0, 1, 1, 2, 3]))])
    if roll < 0.4:
        return Not(_formula(rng, scope, depth - 1))
    if roll < 0.7:
        connective = rng.choice([And, Or, Implies, Iff, Xor, Contrast])
        return connective(_formula(rng, scope, depth - 1), _formula(rng, scope, depth - 1))
    name = rng.choice(_VARIABLES)
    if roll < 0.92:
        return Quantifier(rng.choice("∀∃"), Variable(name), _formula(rng, scope + [name], depth - 1))
    return Count(rng.choice(["ge", "le", "eq"]), Number(rng.randint(0, 3)), Variable(name),
                 _formula(rng, scope + [name], depth - 1))


def _as_written(node):
    """What the text of a node says: an exclusive or is written as ``(l | r) & -(l & r)``."""
    node = node.map_children(_as_written)
    if isinstance(node, Xor):
        return And(Or(node.left, node.right), Not(And(node.left, node.right)))
    return node


def _up_to_bound_names(node, scope=()):
    """The node with every bound variable named by the depth of its binder, a free variable by its lower-case."""
    if isinstance(node, Quantifier):
        name = f"#{len(scope)}"
        return Quantifier(node.type, Variable(name),
                          _up_to_bound_names(node.formula, scope + ((node.variable.name, name),)))
    if isinstance(node, Variable):
        for original, bound in reversed(scope):
            if original == node.name:
                return Variable(bound)
        return Variable("free " + node.name.lower())
    return node.map_children(lambda child: _up_to_bound_names(child, scope))


def test_what_the_problem_writer_writes_is_read_back_as_the_same_formulas(monkeypatch):
    sanitised_lists = []
    original = writer._sanitize_for_prover9

    def remember(formulas, sorts=()):
        result = original(formulas, sorts)
        sanitised_lists.append(result[0])
        return result

    monkeypatch.setattr(writer, "_sanitize_for_prover9", remember)
    rng = random.Random(20261201)
    read_back = refused = 0
    for _ in range(120):
        premises = [_formula(rng, [], rng.randint(1, 4)) for _ in range(rng.randint(0, 2))]
        conclusion = _formula(rng, [], rng.randint(1, 4))
        sanitised_lists.clear()
        try:
            text, _ = writer.generate_prover9_input_with_mapping(premises, conclusion)
        except NotImplementedError:
            refused += 1                  # two variables that differ only in case: refused by name
            continue
        sanitised = sanitised_lists[-1]
        count = len(premises)
        # the file lists the premises, then the sort facts (none here), then the goal
        wanted = sanitised[:count] + sanitised[count + 1:] + [sanitised[count]]
        got = [record.formula for record in parse_prover9_problem(text)]
        assert len(got) == len(wanted), text
        for read, written in zip(got, wanted):
            assert _up_to_bound_names(read) == _up_to_bound_names(_as_written(written)), (text, written)
        read_back += 1
    assert read_back >= 100 and refused <= 20


# --------------------------------------------------------------------------- #
# Z3 through the reader, and the real Prover9 on the text.
# --------------------------------------------------------------------------- #

_BINDERS = ["x", "X", "y", "Y", "Xa", "XA", "xa", "_q", "z", "w", "u", "a1", "A1", "k", "K"]
# names that are constants under each convention when no quantifier binds them
_FREE_CONSTANTS = {
    True: ["a", "b", "c", "alpha", "_k", "x", "y", "z", "w", "u", "xa", "k", "all_a"],
    False: ["a", "b", "c", "alpha", "K", "X", "Y", "Xa", "XA", "_k", "k", "A1", "all_a"],
}
_TEXT_PREDICATES = [("P", 1), ("Q", 2), ("R", 1), ("allowed", 1), ("allergic", 1), ("exists_in", 1), ("all_men", 2),
                    ("existsRoom", 1), ("pP", 1)]
_TEXT_FUNCTIONS = [("f", 1), ("g", 2)]
_CONNECTIVES = {"and": "&", "or": "|", "imp": "->", "iff": "<->", "rimp": "<-"}


def _text_term(rng, scope, prolog, depth):
    roll = rng.random()
    if depth > 0 and roll < 0.2:
        name, arity = rng.choice(_TEXT_FUNCTIONS)
        return (name, [_text_term(rng, scope, prolog, depth - 1) for _ in range(arity)])
    if scope and roll < 0.7:
        return rng.choice(scope)
    return rng.choice(_FREE_CONSTANTS[prolog])


def _text_formula(rng, scope, prolog, depth):
    roll = rng.random()
    if depth <= 0 or roll < 0.3:
        if rng.random() < 0.12:
            return ("eq", _text_term(rng, scope, prolog, 1), _text_term(rng, scope, prolog, 1))
        name, arity = rng.choice(_TEXT_PREDICATES)
        return ("atom", name, [_text_term(rng, scope, prolog, 1) for _ in range(arity)])
    if roll < 0.42:
        return ("not", _text_formula(rng, scope, prolog, depth - 1))
    if roll < 0.75:
        return (rng.choice(list(_CONNECTIVES)), _text_formula(rng, scope, prolog, depth - 1),
                _text_formula(rng, scope, prolog, depth - 1))
    name = rng.choice(_BINDERS)
    return (rng.choice(["all", "exists"]), name, _text_formula(rng, scope + [name], prolog, depth - 1))


def _respell(ast, rng, mapping=None):
    """The same formula with its bound names chosen again."""
    mapping = mapping or {}
    if isinstance(ast, str):
        return mapping.get(ast, ast)
    kind = ast[0]
    if kind in ("all", "exists"):
        new = rng.choice(_BINDERS)
        return (kind, new, _respell(ast[2], rng, {**mapping, ast[1]: new}))
    if kind == "atom":
        return ("atom", ast[1], [_respell(t, rng, mapping) for t in ast[2]])
    if kind == "eq":
        return ("eq", _respell(ast[1], rng, mapping), _respell(ast[2], rng, mapping))
    if kind == "not":
        return ("not", _respell(ast[1], rng, mapping))
    if kind in _CONNECTIVES:
        return (kind, _respell(ast[1], rng, mapping), _respell(ast[2], rng, mapping))
    return (kind, [_respell(t, rng, mapping) for t in ast[1]])      # a function term


def _show_term(term):
    if isinstance(term, str):
        return term
    return f"{term[0]}({', '.join(_show_term(a) for a in term[1])})"


def _show(ast, top=True):
    """Parenthesised, except that a quantifier over an atom stands bare as the operand of ``&`` and ``|``, so
    that its scope ends at the connective."""
    kind = ast[0]
    if kind == "atom":
        return f"{ast[1]}({', '.join(_show_term(a) for a in ast[2])})"
    if kind == "eq":
        return f"{_show_term(ast[1])} = {_show_term(ast[2])}"
    if kind == "not":
        inner = ast[1]
        return f"-{_show(inner, False)}" if inner[0] in ("atom", "not") else f"-({_show(inner)})"
    if kind in ("all", "exists"):
        body = ast[2]
        shown = _show(body, False) if body[0] in ("atom", "not", "all", "exists") else f"({_show(body)})"
        text = f"{kind} {ast[1]} {shown}"
        return text if top else f"({text})"
    left, right = ast[1], ast[2]

    def side(part):
        if part[0] in ("atom", "not", "eq"):
            return _show(part, False)
        if part[0] in ("all", "exists") and kind in ("and", "or"):
            return _show(part, True)
        return f"({_show(part)})"
    text = f"{side(left)} {_CONNECTIVES[kind]} {side(right)}"
    return text if top else f"({text})"


def _file(prolog, premises, goal):
    head = ("set(prolog_style_variables).\n" if prolog else "") + \
        "assign(max_seconds, 6).\nclear(print_initial_clauses).\nclear(print_kept).\nclear(print_given).\n"
    return (head + "formulas(assumptions).\n" + "".join(f"  {_show(p)}.\n" for p in premises)
            + "end_of_list.\nformulas(goals).\n  " + _show(goal) + ".\nend_of_list.\n")


def _random_file(rng):
    prolog = rng.random() < 0.5
    premises = [_text_formula(rng, [], prolog, rng.randint(1, 3)) for _ in range(rng.randint(0, 2))]
    roll = rng.random()
    if roll < 0.35 and premises:
        goal = _respell(premises[0], rng)
    elif roll < 0.5 and premises:
        goal = ("or", premises[0], _text_formula(rng, [], prolog, 2))
    else:
        goal = _text_formula(rng, [], prolog, rng.randint(1, 3))
    return _file(prolog, premises, goal)


def _kit_status(text):
    records = parse_prover9_problem(text)
    premises = [r.formula for r in records if r.role == "assumptions"]
    (goal,) = [r.formula for r in records if r.role == "goals"]
    return api.prove(goal, premises, backends=["z3"], timeout=8000).status


def test_the_random_files_are_read_and_both_kinds_of_verdict_occur():
    rng = random.Random(20261202)
    statuses = [_kit_status(_random_file(rng)) for _ in range(40)]
    assert statuses.count("proved") >= 8 and statuses.count("refuted") >= 8
    assert set(statuses) <= {"proved", "refuted"}


_BINARY = Prover9Backend._binary()
live = pytest.mark.skipif(
    _BINARY is None,
    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or "
           "put 'prover9' on PATH; the offline tests above carry the claim")


def _prover9_outcome(text):
    """``"proved"``, ``"not proved"`` (the search ended: exit 2) or ``"other"`` (a limit, or a refusal)."""
    with tempfile.NamedTemporaryFile("w", suffix=".in", delete=False, encoding="utf-8", newline="\n") as handle:
        handle.write(text)
        path = handle.name
    try:
        command = writer._prover9_command(_BINARY, path, os.environ.get("UFK_PROVER9_WSL") == "1")
        run = subprocess.run(command, capture_output=True, text=True, encoding="utf-8", errors="replace",
                             stdin=subprocess.DEVNULL, timeout=60)
    finally:
        os.unlink(path)
    if "THEOREM PROVED" in run.stdout:
        return "proved"
    return "not proved" if run.returncode == 2 else "other"


@live
def test_z3_through_the_reader_and_the_real_prover9_do_not_give_opposite_verdicts():
    rng = random.Random(20261203)
    opposite, seen = [], {"proved": 0, "refuted": 0}
    for _ in range(24):
        text = _random_file(rng)
        kit, prover9 = _kit_status(text), _prover9_outcome(text)
        assert prover9 != "other", text           # the generated text is one Prover9 reads and finishes
        seen[kit] += 1
        if (kit == "proved") != (prover9 == "proved"):
            opposite.append((kit, prover9, text))
    assert not opposite, opposite[0]
    assert seen["proved"] >= 4 and seen["refuted"] >= 4
