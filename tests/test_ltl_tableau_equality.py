r"""The LTL tableau refuses an identity atom by name, as the modal tableau and the Kripke evaluator do.

The LTL tableau reads an atom as a propositional letter: the elementary atoms of its closure are sets of
rendered atom keys and a counterexample trace is a valuation of those keys. The atom ``dora = dora`` was
such a letter, and the formula ``dora = dora`` had a counterexample in which that letter is false, so
``ltl_decide`` said ``invalid`` and ``api.prove`` said ``refuted`` of a formula that is valid: identity is
reflexive, both sides are the one constant, and the atom is true at every position of every model.

An answer about identity would need a semantics of terms, which the tableau does not have, and reading
``=`` as an unconstrained letter is an approximation the kit refuses. So every entry point refuses an
equality or disequality atom anywhere in its formulas (the goal, a premise, under a temporal operator, in
a sorted constant's annotation position) with ``NotImplementedError`` naming the atom, and the backend
turns that into ``unknown`` with the reason ``unsupported``. The rest of the fragment is unaffected.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp.ltl_tableau import (
    LTLTrace, LtlTableauBackend, ltl_countermodel, ltl_decide, ltl_trace_satisfies, ltl_tableau_closed,
    ltl_valid,
)
from unicode_logic_kit.fol.nodes import (
    And, Always, Atom, Constant, Eventually, Implies, Next, Not, Or, SortedConstant, Until,
)

DORA = Constant("dora")
SAME = Atom("=", [DORA, DORA])
DIFFERENT = Atom("≠", [DORA, Constant("emil")])
P = Atom("p", [])

REFUSED = [
    ("dora = dora", SAME),
    ("a sorted constant on both sides", Atom("=", [SortedConstant("dora", "Human"), SortedConstant("dora", "Animal")])),
    ("Ⓕ dora = dora", Eventually(SAME)),
    ("a disequality", DIFFERENT),
    ("under a negation and a next", Not(Next(Not(SAME)))),
    ("inside an until", Until(P, And(P, SAME))),
    ("next to an ordinary atom", Or(P, SAME)),
]


@pytest.mark.parametrize("name, formula", REFUSED, ids=[r[0] for r in REFUSED])
def test_every_entry_point_refuses_an_identity_atom_by_name(name, formula):
    for entry in (lambda: ltl_decide(formula), lambda: ltl_valid(formula),
                  lambda: ltl_countermodel(formula), lambda: ltl_tableau_closed([formula]),
                  lambda: ltl_decide(P, premises=[formula]),
                  lambda: ltl_decide(formula, mode="floating")):
        with pytest.raises(NotImplementedError) as refusal:
            entry()
        message = str(refusal.value)
        assert message.startswith("ltl_tableau: the ")
        assert "is refused by name" in message
        assert "dora" in message                      # the atom is named, not only its kind


def test_the_evaluator_of_a_trace_refuses_it_too():
    trace = LTLTrace(prefix=(), cycle=(frozenset(),))
    with pytest.raises(NotImplementedError):
        ltl_trace_satisfies(SAME, trace)
    with pytest.raises(NotImplementedError):
        ltl_trace_satisfies(Always(Or(P, DIFFERENT)), trace)


def test_the_backend_answers_unsupported_and_never_refuted():
    verdict = LtlTableauBackend().decide(SAME, [], timeout=5000)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert "dora = dora" in verdict.detail
    through_the_api = api.prove(SAME, [], backends=["ltl-tableau"], logic="modal", timeout=5000)
    assert through_the_api.status == "unknown"            # not "refuted": the formula is valid


def test_the_backend_refuses_an_identity_atom_in_a_premise_too():
    verdict = LtlTableauBackend().decide(P, [SAME], timeout=5000)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert api.prove(P, [SAME], backends=["ltl-tableau"], logic="modal", timeout=5000).status == "unknown"


def test_the_fragment_it_decides_is_unchanged():
    # Gp → p and p → Fp are theorems of linear time (the present is included); p → Xp is not
    assert ltl_decide(Implies(Always(P), P)) == "valid"
    assert ltl_decide(Implies(P, Eventually(P))) == "valid"
    assert ltl_decide(Implies(P, Next(P))) == "invalid"
    trace = ltl_countermodel(Implies(P, Next(P)))
    assert trace is not None and not ltl_trace_satisfies(Implies(P, Next(P)), trace)
    # a predicate that merely mentions a constant is an ordinary letter
    q = Atom("Q", [DORA])
    assert ltl_decide(Implies(Always(q), q)) == "valid"
