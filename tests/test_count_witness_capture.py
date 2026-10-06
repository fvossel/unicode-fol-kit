"""A counting quantifier's witnesses never take the name of a constant in its matrix.

``∃≥n x φ`` is decided by expanding it into ``n`` witness variables. Until 0.30.0
the witnesses avoided the VARIABLE names of ``φ`` only. A constant may be spelled
like a variable — the grammar cannot write one, but the description-logic image
does (an individual named ``y0``), the TPTP reader does (``p(x0)``), and so can
any caller who builds nodes — and ``Variable("y0")`` and ``Constant("y0")`` print
the same and are the same Z3 constant. A witness named ``y0`` therefore CAPTURED
the constant.

Found by an independent OWL 2 oracle run against ``dl.kb_to_fol``: 11 of 4500
generated knowledge bases with individuals named letter-plus-digits were reported
inconsistent although they have a model.

Every expectation below is derived by hand first; the derivation is in the test.
"""
import re

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit import api
from unicode_fol_kit.fol import _identifiers
from unicode_fol_kit.fol.nodes import (Atom, Constant, Count, Not, Number,
                                        Quantifier, Variable)

# Not a shrunken budget: "unknown" is not a verdict, and a test built on one
# would assert nothing.
TIMEOUT_MS = 30000

X = Variable("x")
#: ∀x ¬R(x, x)
IRREFLEXIVE = Quantifier("∀", X, Not(Atom("R", (X, X))))


def _status(goal, premises):
    status = api.prove(goal, premises, backends=["z3"], timeout=TIMEOUT_MS).status
    assert status in ("proved", "refuted"), status
    return status


def _bound_names(node):
    return {n.variable.name for n in node.walk() if isinstance(n, Quantifier)}


@pytest.mark.parametrize("constant", ["x0", "x1", "y0", "w3"])
@pytest.mark.parametrize("bound", [1, 2, 3])
def test_no_witness_is_named_like_a_constant_of_the_matrix(constant, bound):
    # ∃≥n x R(c, x), with the constant c spelled like a variable. Whatever the
    # witnesses are called, none may be called c: a quantifier binding the name
    # c would turn the constant into a bound variable.
    count = Count("ge", Number(bound), X, Atom("R", (Constant(constant), X)))
    expansion = count._expand()
    assert constant not in _bound_names(expansion)
    # and the constant is still there, as a constant, once per witness
    constants = [n for n in expansion.walk() if isinstance(n, Constant)]
    assert [c.name for c in constants] == [constant] * bound
    # the witnesses are still legal variable names of this kit
    for name in _bound_names(expansion):
        assert re.fullmatch(_identifiers.variable_pattern(), name), name


def test_the_expansion_means_what_the_count_means():
    # Premise: R is irreflexive. Question: does ¬∃≥1 x R(c, x) follow, for the
    # constant c named "x0"?
    #
    # By hand: NO. Take two elements 0 and 1, c = 0 and R = {(0, 1)}. R is
    # irreflexive and c has an R-successor, so ∃≥1 x R(c, x) is true there.
    # The capturing expansion was ∃x0 R(x0, x0) — "something is R-related to
    # itself" — which irreflexivity refutes, so the negation came out PROVED.
    c = Constant("x0")
    has_successor = Count("ge", Number(1), X, Atom("R", (c, X)))
    assert _status(Not(has_successor), [IRREFLEXIVE]) == "refuted"
    # The control, where the loop really is what is said: ∃≥1 x R(x, x) is
    # refuted by irreflexivity, so its negation IS a consequence.
    has_loop = Count("ge", Number(1), X, Atom("R", (X, X)))
    assert _status(Not(has_loop), [IRREFLEXIVE]) == "proved"


def test_an_individual_named_like_a_variable_keeps_a_consistent_knowledge_base_consistent():
    # r is irreflexive; y0 : ≥1 r.⊤.
    # By hand: y0 needs an r-successor, and irreflexivity only says it is not
    # y0 itself. Two elements, r = {(y0, e)}: a model. CONSISTENT — on both
    # routes, which is the point of having two.
    tbox = dl.TBox().add_irreflexive_role("r")
    abox = dl.ABox().assert_concept("y0", dl.AtLeast(1, "r", dl.Top()))
    assert dl.abox_consistent(abox, tbox) is True
    kb = dl.kb_to_fol(tbox, abox)
    assert kb.refutation_is_decisive is True          # no data layer: a faithful image
    assert _status(Not(kb.formula), list(kb.axioms)) == "refuted"
    # The control: the same knowledge base plus "y0 has NO r-successor" has no model.
    clash = abox.assert_concept("y0", dl.AtMost(0, "r", dl.Top()))
    assert dl.abox_consistent(clash, tbox) is False
    kb = dl.kb_to_fol(tbox, clash)
    assert _status(Not(kb.formula), list(kb.axioms)) == "proved"


@pytest.mark.parametrize("individual", ["y0", "x0", "x1", "w0", "v0"])
def test_a_data_count_over_such_an_individual_proves_nothing_it_should_not(individual):
    # <individual> : ≥1 g.xsd:string, and the question "is <individual> an A?".
    # By hand: one object with one string g-value, A empty, is an OWL model of
    # the knowledge base in which the answer is NO. So the goal must not be
    # proved and the knowledge base must not be proved inconsistent. (The
    # captured witness contradicted the typing axioms — an object that is its
    # own data value — and from an inconsistent image everything follows.)
    abox = dl.ABox().assert_concept(
        individual, dl.DataAtLeast(1, "g", dl.Datatype("xsd:string")))
    kb = dl.kb_to_fol(dl.TBox(), abox, query=[dl.Atomic("A")])
    goal = kb.instance_goal(individual, dl.Atomic("A"))
    assert _status(goal, list(kb.premises)) == "refuted"
    assert _status(Not(kb.formula), list(kb.axioms)) == "refuted"


@pytest.mark.parametrize("render", ["to_tptp", "to_prover9"])
def test_the_text_renderers_keep_the_constant_a_constant(render):
    # Both renderers write a variable with an upper-case first letter and a
    # constant in lower case. ∃≥1 x r(x0c, x) with the constant x0: the text
    # must contain the constant "x0" and must not bind a variable "X0".
    count = Count("ge", Number(1), X, Atom("r", (Constant("x0"), X)))
    text = getattr(count, render)()
    assert "x0" in text
    assert "X0" not in text
