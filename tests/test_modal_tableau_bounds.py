"""The labelled modal tableau ends its search at a deadline and at the recursion limit, and says so.

Three bounds end the search: ``max_worlds`` / ``max_steps``, an optional wall-clock ``timeout`` in
milliseconds (read at every step), and Python's recursion limit (the search recurses once per branching
formula along a branch). Every one of them gives ``"unknown"`` (``modal_decide``) or "not closed"
(the boolean entry points); none raises.

The workload is the propositional pigeonhole principle: "every pigeon sits in a hole and no hole holds two"
is unsatisfiable for more pigeons than holes, so its negation is valid, and the tableau needs a search
that grows steeply with the size: PHP(3,2) closes at once, PHP(4,3) takes seconds.
"""

import inspect
import sys
import time

from unicode_logic_kit.atp.modal_tableau import (
    is_modal_valid, modal_countermodel, modal_decide, modal_prove, modal_tableau_closed,
)
from unicode_logic_kit.atp.protocol import UNKNOWN, get_backend
from unicode_logic_kit.fol.nodes import And, Atom, Not, Or


def _pigeonhole(pigeons, holes):
    p = lambda i, j: Atom(f"P{i}x{j}", [])
    parts = []
    for i in range(pigeons):
        row = p(i, 0)
        for j in range(1, holes):
            row = Or(row, p(i, j))
        parts.append(row)
    for j in range(holes):
        for i in range(pigeons):
            for k in range(i + 1, pigeons):
                parts.append(Not(And(p(i, j), p(k, j))))
    formula = parts[0]
    for part in parts[1:]:
        formula = And(formula, part)
    return formula


def test_a_deadline_is_a_bound_for_every_entry_point():
    php = _pigeonhole(4, 3)
    for run in (lambda: modal_decide(Not(php), max_steps=10 ** 9, timeout=100),
                lambda: is_modal_valid(Not(php), max_steps=10 ** 9, timeout=100),
                lambda: modal_tableau_closed([php], max_steps=10 ** 9, timeout=100),
                lambda: modal_prove([], Not(php), max_steps=10 ** 9, timeout=100),
                lambda: modal_countermodel(Not(php), max_steps=10 ** 9, timeout=100)):
        start = time.perf_counter()
        answer = run()
        assert time.perf_counter() - start < 5.0
        assert answer in ("unknown", False, None), answer


def test_a_small_pigeonhole_is_still_valid_within_a_generous_limit():
    assert modal_decide(Not(_pigeonhole(3, 2)), timeout=60000) == "valid"


def test_the_backend_reports_a_used_up_limit_as_a_timeout():
    start = time.perf_counter()
    verdict = get_backend("modal-tableau").decide(Not(_pigeonhole(4, 3)), [], timeout=100,
                                                  max_steps=10 ** 9)
    assert time.perf_counter() - start < 5.0
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"


def _balanced_conjunction(parts):
    if len(parts) == 1:
        return parts[0]
    middle = len(parts) // 2
    return And(_balanced_conjunction(parts[:middle]), _balanced_conjunction(parts[middle:]))


def test_more_branching_formulas_than_the_recursion_limit_is_a_bound_not_an_exception():
    # n disjunctions (Pi ∨ Qi) at one world, in a balanced tree (so the formula itself is shallow). The
    # search chooses a disjunct for each in turn, one nested call apiece. The limit is lowered to a
    # little above the depth the test starts from, so that n = 400 exceeds it without a minute of work.
    n = 400
    conjunction = _balanced_conjunction([Or(Atom(f"P{i}", []), Atom(f"Q{i}", [])) for i in range(n)])
    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(len(inspect.stack(0)) + 150)
    try:
        assert modal_decide(Not(conjunction), max_steps=10 ** 7) == "unknown"
        assert is_modal_valid(Not(conjunction), max_steps=10 ** 7) is False
        verdict = get_backend("modal-tableau").decide(Not(conjunction), [], timeout=60000, max_steps=10 ** 7)
        assert verdict.status == UNKNOWN and verdict.reason == "bound_hit"
    finally:
        sys.setrecursionlimit(previous)


def test_fewer_branching_formulas_than_the_limit_are_decided():
    # the same shape, small: an open branch, and "invalid" with a verified countermodel
    conjunction = _balanced_conjunction([Or(Atom(f"P{i}", []), Atom(f"Q{i}", [])) for i in range(20)])
    assert modal_decide(Not(conjunction)) == "invalid"
