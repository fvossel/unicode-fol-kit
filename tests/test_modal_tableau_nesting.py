r"""A formula nested deeper than the labelled modal tableau can walk is "unknown", never an exception.

Every walk over a formula of the tableau is recursive: the scan for equality and for announcements, the
scan for hybrid constructs, the removal of sort annotations, the hash of a node, and the search itself
(once per branching formula along a branch). A formula nested past the interpreter's recursion limit ends
one of them in a ``RecursionError``. The module promises that past a bound the answer is ``("unknown",
None)``, and the answer of an entry point that was not able to read a formula to its end can only be that:
nothing may be said about it.

The inputs are built from nodes (the parser has a depth of its own) and nested three times as deep as the
recursion limit; what each is, by hand:

* ``¬ⁿ p`` is ``p`` for even ``n`` and ``¬p`` for odd ``n``: not valid, so its negation has a model.
* ``¬ⁿ p ↔ p`` for even ``n`` is valid (``¬¬φ ≡ φ``), and so is ``□ⁿ (p → p)`` (a tautology under
  necessitation).
* ``¬◇(a(n-1) ∧ ◇(a(n-2) ∧ … ◇ a0))`` is not valid in K: it says that no chain of ``n`` worlds with those
  atoms starts at the root, and the model that has one falsifies it.

So an answer is either the true one or ``unknown``; the wrong one (``invalid`` for a valid formula, ``valid``
for an invalid one) is never right, and an exception is never right.
"""

import sys

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp import modal_tableau as MT
from unicode_logic_kit.atp.protocol import ModalTableauBackend
from unicode_logic_kit.fol.nodes import And, Atom, Box, Constant, Diamond, Iff, Implies, Not

P = Atom("p", [])
DEPTH = max(1500, 3 * sys.getrecursionlimit())


def _negations(n, formula=P):
    for _ in range(n):
        formula = Not(formula)
    return formula


def _boxes(n, formula):
    for _ in range(n):
        formula = Box(formula)
    return formula


def _chain(n):
    deep = Atom("a0", [])
    for i in range(1, n):
        deep = And(Atom(f"a{i}", []), Diamond(deep))
    return Not(Diamond(deep))


#: (name, formula, truth): ``True`` valid, ``False`` not valid
CASES = [
    ("negations, even", lambda: _negations(DEPTH), False),
    ("negations, odd", lambda: _negations(DEPTH + 1), False),
    ("double negation law", lambda: Iff(_negations(DEPTH), P), True),
    ("necessitated tautology", lambda: _boxes(DEPTH, Implies(P, P)), True),
    ("chain of diamonds", lambda: _chain(DEPTH // 2), False),
]


def _allowed(decision, truth):
    return decision in (("valid", "unknown") if truth else ("invalid", "unknown"))


@pytest.mark.parametrize("name, build, truth", CASES, ids=[c[0] for c in CASES])
@pytest.mark.parametrize("frame", ["K", "S4"])
def test_no_entry_point_raises_and_none_says_what_is_false(name, build, truth, frame):
    formula = build()
    assert _allowed(MT.modal_decide(formula, frame=frame, timeout=5000), truth)
    closed = MT.is_modal_valid(formula, frame=frame, timeout=5000)
    assert closed is False or truth                       # True only for a valid formula
    assert MT.modal_prove([], formula, frame=frame, timeout=5000) is False or truth
    assert MT.modal_tableau_closed([Not(formula)], frame=frame, timeout=5000) is False or truth
    model = MT.modal_countermodel(formula, frame=frame, timeout=5000)
    assert model is None or not truth                     # a countermodel only for a formula that has one


@pytest.mark.parametrize("name, build, truth", CASES, ids=[c[0] for c in CASES])
def test_api_prove_answers_unknown_or_the_truth_never_error(name, build, truth):
    verdict = api.prove(build(), [], backends=["modal-tableau"], logic="modal", timeout=5000)
    assert verdict.status in (("proved", "unknown") if truth else ("refuted", "unknown")), verdict


def test_the_backend_says_why_it_has_no_answer():
    verdict = ModalTableauBackend().decide(_negations(DEPTH), [], timeout=5000)
    assert verdict.status == "unknown"
    assert verdict.reason == "bound_hit"
    assert "nested" in verdict.detail


def test_many_premises_folded_into_one_deep_conjunction_are_no_exception_either():
    # the backend folds the premises into one left-nested conjunction: one level per premise
    premises = [Atom(f"r{i}", []) for i in range(DEPTH)]
    verdict = api.prove(Atom("goal", []), premises, backends=["modal-tableau"], logic="modal", timeout=5000)
    assert verdict.status in ("unknown", "refuted")       # r0 ∧ … ⊬ goal; unknown is as honest


def test_a_wrong_argument_is_refused_whatever_the_depth():
    with pytest.raises(ValueError):
        MT.modal_decide(_negations(DEPTH), frame="no such system")
    with pytest.raises(NotImplementedError):
        MT.modal_decide(_negations(DEPTH), frame="K", bridges="sincerity")


def test_a_construct_the_tableau_refuses_is_still_refused_when_it_can_be_found():
    # nested shallowly, so that the scan reads it: refused by name, as before
    shallow = _negations(50, Atom("=", [Constant("dora"), Constant("dora")]))
    with pytest.raises(NotImplementedError):
        MT.modal_decide(shallow)
    # nested so deeply that the scan cannot read it to its end: unknown, never a verdict
    deep = _negations(DEPTH, Atom("=", [Constant("dora"), Constant("dora")]))
    try:
        answer = MT.modal_decide(deep)
    except NotImplementedError:
        return
    assert answer == "unknown"
