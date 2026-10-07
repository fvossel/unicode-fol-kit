"""cvc5 and many-sorted input: membership of a sorted constant, and sort and constant NAMES.

Two things are pinned here.

1. ``∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)`` is valid -- a sorted constant ``c:S`` is an element
   of ``S`` -- and cvc5 gets that fact the way Z3 does: a membership atom ``S(c)`` per sorted constant,
   next to the non-emptiness of every sort, asserted outside the negated goal and left out of the
   reported unsat core.

2. The SMT-LIB text cvc5 reads has to be built from names that are legal SMT-LIB symbols. Z3 prints a
   digit-leading ASCII name (``2008x``) and a name of SMT-LIB's own vocabulary (``not``, ``let``)
   unquoted, and cvc5 answers that text by ending the Python process. A sorted constant ``2008x:S`` used
   to bypass the renaming altogether (the renamer knew ``Constant`` but not ``SortedConstant``), and a sort
   name never went through it, so a digit-leading one reached cvc5 as it was. Every decision below that
   could end the process runs in a CHILD process, so that a regression is a failed assertion about an exit
   code and not the death of the test run.

Hand-derived expectations (one universe; a sort is the non-empty extension of the unary predicate of its
name; ``c:S`` is an element of ``S``; ``c:S`` and a plain ``c`` are one constant):

* ``∀x:S P(x) ⊢ P(2008x:S)`` is VALID (2008x is an S, every S is P); ``⊢ P(2008x:S)`` is NOT
  (universe {0}, S = {0}, P = {}, 2008x = 0).
* ``∀x:2S P(x) ⊢ ∃x:2S P(x)`` is VALID (2S is not empty); so is ``∀x:2S P(x) ⊢ P(kay:2S)``.
* ``P(2008x), ∀x (P(x) → Q(x)) ⊢ Q(2008x:S)`` is VALID: one constant, written plain once and sorted once.
  With the premise about ``2008y`` instead it is NOT (two constants).
* ``P(2008x), R(2008x:S) ⊢ ∃y:S P(y)`` is VALID: the sorted occurrence puts the constant in S, the plain one
  is P.
"""
import json
import subprocess
import sys

import pytest

pytest.importorskip("cvc5")

from unicode_logic_kit import api
from unicode_logic_kit.atp.cvc5_backend import _sanitize_many_for_smtlib
from unicode_logic_kit.fol.nodes import (
    Atom, Constant, Node, SortedConstant, SortedQuantifier, Variable,
)

_CHILD = r"""
import json, sys
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
from unicode_logic_kit.fol.nodes import Node

spec = json.loads(sys.argv[1])
premises = [Node.from_dict(d) for d in spec["premises"]]
goal = Node.from_dict(spec["goal"])
verdict = Cvc5Backend().decide(goal, premises, timeout=20000)
print(json.dumps({"status": verdict.status,
                  "core": (verdict.proof or {}).get("unsat_core"),
                  "detail": verdict.detail}))
"""

X = Variable("x")


def _decide(premises, goal):
    """Run ``Cvc5Backend().decide`` in a child process; return ``(exit code, parsed output)``."""
    spec = json.dumps({"premises": [p.to_dict() for p in premises], "goal": goal.to_dict()})
    done = subprocess.run([sys.executable, "-c", _CHILD, spec],
                          capture_output=True, text=True, timeout=300)
    out = json.loads(done.stdout.strip().splitlines()[-1]) if done.returncode == 0 else None
    return done.returncode, out


def _status(premises, goal):
    code, out = _decide(premises, goal)
    assert code == 0, f"the child process died with exit code {code}"
    return out["status"]


def F(text) -> Node:
    parsed = api.parse_any(text)
    assert parsed.ok, (text, parsed)
    return parsed.formula


def _all(sort, predicate="P"):
    return SortedQuantifier("∀", X, sort, Atom(predicate, [X]))


def _some(sort, predicate="P"):
    return SortedQuantifier("∃", X, sort, Atom(predicate, [X]))


def _some_with_p(sort):
    return SortedQuantifier("∃", Variable("y"), sort, Atom("P", [Variable("y")]))


# ---------------------------------------------------------------------------------------------
# membership
# ---------------------------------------------------------------------------------------------
def test_cvc5_proves_that_a_sorted_constant_is_in_its_sort():
    assert _status([F("∀x:Human Mortal(x)")], F("Mortal(socrates:Human)")) == "proved"


def test_cvc5_does_not_prove_the_membership_for_an_unsorted_constant():
    # universe {0, 1}, Human = {0}, Mortal = {0}, socrates = 1: cvc5 may say refuted or unknown, never proved
    assert _status([F("∀x:Human Mortal(x)")], F("Mortal(socrates)")) != "proved"


def test_the_membership_atom_is_outside_the_negated_goal():
    # nothing follows about a sorted constant from nothing: universe {0}, Human = {0}, Mortal = {}
    assert _status([], F("Mortal(socrates:Human)")) == "refuted"
    # the sorted constant is its own witness; under the goal's negation the fact would not be there
    assert _status([], F("∃x:Human x = socrates:Human")) == "proved"


def test_the_reported_unsat_core_holds_no_membership_atom_and_no_non_emptiness_axiom():
    premises = [F("∀x:Human Mortal(x)"), F("Bird(tweety)")]
    code, out = _decide(premises, F("Mortal(socrates:Human)"))
    assert code == 0 and out["status"] == "proved"
    core = [entry.strip() for entry in out["core"]]
    # the premise (a universal over Human) and the negated goal are the entries; the membership atom
    # Human(socrates) and "some Human exists" are background facts
    assert "(Human socrates)" not in core, core
    assert not any(entry.startswith("(exists") for entry in core), core
    assert any(entry.startswith("(forall") and "Mortal" in entry for entry in core), core


def test_a_premise_that_equals_the_membership_atom_does_not_confuse_the_verdict_or_the_core():
    # the premise Human(socrates) is identical to the membership atom the backend adds, so it is
    # absorbed into the background in the reported core; the verdict is the same either way
    premises = [F("∀x:Human Mortal(x)"), F("Human(socrates)")]
    code, out = _decide(premises, F("Mortal(socrates:Human)"))
    assert code == 0 and out["status"] == "proved"
    assert not any(entry.strip().startswith("(exists") for entry in out["core"]), out["core"]
    # with an UNSORTED goal the premise Human(socrates) does the work (there is no sorted constant at all)
    assert _status(premises, F("Mortal(socrates)")) == "proved"


# ---------------------------------------------------------------------------------------------
# a digit-leading sorted constant
# ---------------------------------------------------------------------------------------------
def test_a_digit_leading_sorted_constant_is_decided_and_does_not_end_the_process():
    constant = SortedConstant("2008x", "S")
    assert _status([_all("S")], Atom("P", [constant])) == "proved"
    assert _status([], Atom("P", [constant])) == "refuted"


def test_a_sorted_and_a_plain_constant_of_one_name_are_one_symbol_for_cvc5():
    plain, sorted_ = Constant("2008x"), SortedConstant("2008x", "S")
    implication = F("∀x (P(x) → Q(x))")
    assert _status([Atom("P", [plain]), implication], Atom("Q", [sorted_])) == "proved"
    # two different names stay two constants
    other = Constant("2008y")
    assert _status([Atom("P", [other]), implication], Atom("Q", [sorted_])) != "proved"
    # the sorted occurrence puts the constant in S, the plain one is P
    premises = [Atom("P", [plain]), Atom("R", [sorted_])]
    assert _status(premises, _some_with_p("S")) == "proved"


def test_the_sanitiser_renames_a_sorted_and_a_plain_constant_of_one_name_alike():
    plain, sorted_ = Constant("2008x"), SortedConstant("2008x", "S")
    (a, b), names = _sanitize_many_for_smtlib([Atom("P", [plain]), Atom("Q", [sorted_])])
    token = names.get("2008x")
    assert token != "2008x" and token[0].isalpha()
    assert a.args[0] == Constant(token)
    assert b.args[0] == SortedConstant(token, "S")      # the sort S is a legal name and stays


# ---------------------------------------------------------------------------------------------
# sort names
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("sort", ["2S", "2008Summer", "not", "let", "distinct"])
def test_a_sort_name_that_is_no_legal_smtlib_symbol_is_renamed_and_does_not_end_the_process(sort):
    # not empty, whatever it is called: ∀x:S P(x) ⊢ ∃x:S P(x)
    assert _status([_all(sort)], _some(sort)) == "proved"
    # a sorted constant of such a sort is an element of it
    assert _status([_all(sort)], Atom("P", [SortedConstant("kay", sort)])) == "proved"
    # and the guard is still not trivial: nothing about P follows for a constant of ANOTHER sort
    assert _status([_all(sort)], Atom("P", [SortedConstant("kay", "T")])) != "proved"


def test_the_sanitiser_gives_a_sort_name_and_the_predicate_of_that_name_one_token():
    # the sort and the unary predicate of one name are ONE symbol, in the renaming as everywhere
    (quantified, atom), names = _sanitize_many_for_smtlib([_all("2S"), Atom("2S", [Constant("kay")])])
    token = names.get("2S")
    assert token != "2S" and token[0].isalpha()
    assert quantified.sort == token
    assert atom.predicate == token


def test_a_legal_non_ascii_sort_name_is_left_alone():
    # Z3 quotes it correctly; renaming a name the backend already handles would be an unforced change
    (quantified,), names = _sanitize_many_for_smtlib([_all("Süß")])
    assert quantified.sort == "Süß" and names.get("Süß") == "Süß"

