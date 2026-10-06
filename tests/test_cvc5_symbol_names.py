"""A symbol of this kit named like a theory symbol of SMT-LIB is still an
uninterpreted symbol — and never a crash.

The cvc5 backend hands cvc5 the SMT-LIB text Z3 prints for the problem. Until
0.30.0 it set the logic ``ALL``, under which cvc5 knows hundreds of names with a
fixed signature. A predicate ``<`` or a function ``+`` / ``select`` / ``sin`` /
``not`` of this kit is declared as an uninterpreted symbol over the one sort, and
cvc5's parser answered that declaration by ending the Python process with a
native access violation: no exception, no verdict, nothing to catch. The data
layer of the description-logic package reaches it with one ordering facet
(``∀x ∀v (d(x, v) → v < 2)``), and ``api.prove`` runs cvc5 whenever Z3 is not
definitive.

Every case runs in a CHILD process, so that a regression is a failed assertion
about an exit code and not the death of the test run.
"""
import json
import subprocess
import sys

import pytest

pytest.importorskip("cvc5")

_CHILD = r"""
import json, sys
from unicode_fol_kit.atp.cvc5_backend import Cvc5Backend
from unicode_fol_kit.fol.nodes import (Atom, Constant, Function, Implies,
                                        Quantifier, Variable)

kind, name = sys.argv[1], sys.argv[2]
a, b, x = Constant("ca"), Constant("cb"), Variable("x")
P = lambda t: Atom("P", (t,))
if kind == "predicate":
    # ∀x (P(x) → name(x, cb))  ⊢  P(ca) → name(ca, cb)          one instantiation
    entailed = ([Quantifier("∀", x, Implies(P(x), Atom(name, (x, b))))],
                Implies(P(a), Atom(name, (a, b))))
    # P(ca)  ⊬  name(ca, cb)        model: P = {ca}, name empty
    not_entailed = ([P(a)], Atom(name, (a, b)))
elif kind == "function":
    # ∀x P(name(x, cb))  ⊢  P(name(ca, cb))
    entailed = ([Quantifier("∀", x, P(Function(name, (x, b))))],
                P(Function(name, (a, b))))
    # P(ca)  ⊬  P(name(ca, cb))     model: two elements, name(...) the other one
    not_entailed = ([P(a)], P(Function(name, (a, b))))
else:
    # P(name)  ⊢  P(name), with the constant called `name`
    entailed = ([P(Constant(name))], P(Constant(name)))
    # P(ca)  ⊬  P(name)             model: two elements, P true of one
    not_entailed = ([P(a)], P(Constant(name)))
out = {}
for label, (premises, goal) in (("entailed", entailed), ("not_entailed", not_entailed)):
    out[label] = Cvc5Backend().decide(goal, premises, timeout=20000).status
print(json.dumps(out))
"""

#: Core symbols (known to cvc5 under every logic) and theory symbols of the
#: logics ``ALL`` adds. Each was measured to crash or to be refused before.
_NAMES = [
    ("predicate", "<"), ("predicate", "<="), ("predicate", ">"), ("predicate", ">="),
    ("predicate", "distinct"), ("predicate", "=>"), ("predicate", "xor"),
    ("predicate", "and"), ("predicate", "or"),
    ("function", "+"), ("function", "-"), ("function", "div"), ("function", "mod"),
    ("function", "select"), ("function", "store"), ("function", "concat"),
    ("function", "and"), ("function", "ite"),
    ("constant", "true"), ("constant", "false"),
    # and the control: a name that never was a problem
    ("predicate", "Likes"), ("function", "f"), ("constant", "cc"),
]


def _run(*argv, source=_CHILD):
    done = subprocess.run([sys.executable, "-c", source, *argv],
                          capture_output=True, text=True, timeout=300)
    return done


@pytest.mark.parametrize("kind, name", _NAMES, ids=[f"{k}:{n}" for k, n in _NAMES])
def test_a_symbol_named_like_a_theory_symbol_is_uninterpreted_and_decided(kind, name):
    done = _run(kind, name)
    # 0, not 3221225477 (Windows access violation) or -11 (SIGSEGV)
    assert done.returncode == 0, (done.returncode, done.stderr[-400:])
    verdicts = json.loads(done.stdout.strip().splitlines()[-1])
    # Hand-derived in the child's comments: the first is one instantiation (or
    # an identity), the second has a two-element countermodel — whatever the
    # symbol is called, because it is uninterpreted.
    assert verdicts == {"entailed": "proved", "not_entailed": "refuted"}


_FACET = r"""
import unicode_fol_kit.dl as dl
from unicode_fol_kit.atp.cvc5_backend import Cvc5Backend

# range(d) = xsd:integer[< 2]: the image has the premise ∀x ∀v (d(x, v) → … ∧ v < 2).
tbox = dl.TBox().add_data_property_range("d", dl.DatatypeRestriction(
    dl.Datatype("xsd:integer"), (("xsd:maxExclusive", dl.Literal("2", "xsd:integer")),)))
kb = dl.kb_to_fol(tbox, query=[dl.Atomic("A")])
verdict = Cvc5Backend().decide(kb.unsatisfiability_goal(dl.Atomic("A")),
                               list(kb.tbox_premises), timeout=10000)
print(verdict.status)
"""


def test_an_ordering_facet_of_the_data_layer_reaches_cvc5_without_killing_the_process():
    done = _run(source=_FACET)
    assert done.returncode == 0, (done.returncode, done.stderr[-400:])
    # By hand: nothing in the knowledge base mentions A, so A is satisfiable
    # (one object in A, d empty) and "A is unsatisfiable" must NOT be proved.
    # cvc5 may answer refuted or unknown for this quantified problem; either is
    # honest, a proof would be a wrong answer.
    assert done.stdout.strip().splitlines()[-1] in ("refuted", "unknown")
