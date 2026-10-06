"""The Kripke enumerator ends at its deadline (``timeout``, milliseconds), and says that it did.

``modal_enum_search`` takes ``timeout`` (default ``None``: no limit, the search is the one it always
was). A search it cut off has ``timed_out=True``, no model, and ``exhausted=False``: no countermodel was
found, and the space was not covered either. The ``kripke-enum`` backend reports ``unknown`` with
reason ``timeout`` for it, and ``bound_hit`` for an exhausted or a budget-limited search.

Three workloads, each far beyond any limit used here:

* the negated propositional pigeonhole principle, ``¬PHP(4, 3)``: "every pigeon sits in a hole, no
  hole holds two" has no model for four pigeons and three holes, so the negation is valid and there
  is no countermodel to find; it has 12 atoms, so the default budget of 200000 candidate models is
  the only bound, and it takes minutes to spend (about 4 ms a model);
* a valid formula over 8 atoms on S5 with three worlds, whose valuations number ``2 ** 24`` for
  three worlds;
* ``□p → □□p`` (valid on S4) over up to five worlds: the transitive reflexive relations over five
  worlds are found among ``2 ** 25`` edge sets.
"""

import time

from unicode_fol_kit import api
from unicode_fol_kit.atp import hybrid_down, kripke_enum
from unicode_fol_kit.atp.kripke_enum import (
    KripkeEnumBackend, modal_enum_countermodel, modal_enum_search,
)
from unicode_fol_kit.atp.protocol import REFUTED, UNKNOWN, declared_options, get_backend
from unicode_fol_kit.fol.nodes import And, Atom, Box, Diamond, Implies, Not, Or

#: A call must end within its limit plus this much.
SLACK = 5.0

P = Atom("p", [])


def _conjunction(parts):
    out = parts[0]
    for part in parts[1:]:
        out = And(out, part)
    return out


def _pigeonhole(pigeons, holes):
    """Every pigeon sits in a hole and no hole holds two."""
    atom = lambda i, j: Atom(f"P{i}x{j}", [])
    rows = []
    for i in range(pigeons):
        row = atom(i, 0)
        for j in range(1, holes):
            row = Or(row, atom(i, j))
        rows.append(row)
    for j in range(holes):
        for i in range(pigeons):
            for k in range(i + 1, pigeons):
                rows.append(Not(And(atom(i, j), atom(k, j))))
    return _conjunction(rows)


NO_COUNTERMODEL = Not(_pigeonhole(4, 3))
TAUTOLOGY_OVER_EIGHT_ATOMS = Box(_conjunction([Or(Atom(f"q{i}", []), Not(Atom(f"q{i}", []))) for i in range(8)]))
S4_AXIOM_4 = Implies(Box(P), Box(Box(P)))
DUALITY = Implies(Box(P), Not(Diamond(Not(P))))        # valid over every frame


def test_a_search_with_a_budget_of_minutes_is_cut_off_at_its_deadline():
    start = time.perf_counter()
    result = modal_enum_search(NO_COUNTERMODEL, timeout=300)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert result.timed_out is True
    assert result.model is None and result.exhausted is False and result.unsupported is None
    assert 0 <= result.checked < 200000
    assert "300 ms" in result.detail


def test_a_valid_formula_over_many_atoms_is_cut_off_at_its_deadline():
    # eight atoms: 2 ** 16 valuations for two worlds, 2 ** 24 for three
    start = time.perf_counter()
    result = modal_enum_search(TAUTOLOGY_OVER_EIGHT_ATOMS, frame="S5", max_worlds=3, timeout=500)
    assert time.perf_counter() - start < 0.5 + SLACK
    assert result.timed_out is True and result.model is None


def test_relations_that_cannot_be_enumerated_are_not_waited_for():
    # over five worlds there are 2 ** 25 edge sets to test against reflexivity and transitivity
    start = time.perf_counter()
    result = modal_enum_search(S4_AXIOM_4, frame="S4", max_worlds=5, timeout=400)
    assert time.perf_counter() - start < 0.4 + SLACK
    assert result.timed_out is True and result.model is None and result.exhausted is False


def test_a_deadline_that_has_passed_ends_the_search_before_the_first_candidate():
    result = modal_enum_search(S4_AXIOM_4, timeout=-1)
    assert result.timed_out is True and result.checked == 0 and result.model is None


def test_a_search_that_finds_its_model_in_time_is_the_search_without_a_limit():
    # □p → □□p is not valid over K: a countermodel exists, and the limit changes nothing
    plain = modal_enum_search(S4_AXIOM_4)
    timed = modal_enum_search(S4_AXIOM_4, timeout=60_000)
    assert plain.model is not None and plain.timed_out is False
    assert timed.to_dict() == plain.to_dict()


def test_a_search_that_is_complete_in_time_is_exhausted_and_not_a_timeout():
    # p → p is valid: every candidate up to two worlds is checked, and none refutes it
    plain = modal_enum_search(Implies(P, P), max_worlds=2)
    timed = modal_enum_search(Implies(P, P), max_worlds=2, timeout=60_000)
    assert plain.exhausted is True
    assert timed.exhausted is True and timed.timed_out is False
    assert timed.to_dict() == plain.to_dict()


def test_the_countermodel_wrapper_takes_the_limit_too():
    start = time.perf_counter()
    assert modal_enum_countermodel(NO_COUNTERMODEL, timeout=300) is None
    assert time.perf_counter() - start < 0.3 + SLACK
    assert modal_enum_countermodel(S4_AXIOM_4, timeout=60_000) is not None


def test_a_result_records_the_deadline_in_its_dictionary_form():
    assert modal_enum_search(S4_AXIOM_4, timeout=-1).to_dict()["timed_out"] is True
    assert modal_enum_search(S4_AXIOM_4).to_dict()["timed_out"] is False


# ---------------------------------------------------------------------------------------------
# the backend, and what is built on it
# ---------------------------------------------------------------------------------------------
def test_the_backend_reports_a_cut_off_search_as_a_timeout():
    start = time.perf_counter()
    verdict = KripkeEnumBackend().decide(NO_COUNTERMODEL, timeout=300)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"
    assert verdict.logic == "modal"


def test_the_backend_reports_a_complete_search_as_bound_hit():
    verdict = KripkeEnumBackend().decide(Implies(P, P), timeout=60_000, max_worlds=2)
    assert verdict.status == UNKNOWN and verdict.reason == "bound_hit"


def test_the_backend_reports_a_spent_budget_as_bound_hit_and_not_as_a_timeout():
    verdict = KripkeEnumBackend().decide(NO_COUNTERMODEL, timeout=60_000, max_models=50)
    assert verdict.status == UNKNOWN and verdict.reason == "bound_hit"


def test_the_backend_still_refutes_with_a_limit():
    verdict = KripkeEnumBackend().decide(S4_AXIOM_4, timeout=60_000)
    assert verdict.status == REFUTED


def test_a_chain_of_the_backend_ends_at_the_limit_of_the_call():
    start = time.perf_counter()
    verdict = api.prove(NO_COUNTERMODEL, [], backends=["kripke-enum"], logic="modal", timeout=300)
    assert time.perf_counter() - start < 0.3 + SLACK
    assert verdict.status == UNKNOWN
    assert "kripke-enum:unknown/timeout" in verdict.detail


def test_the_limit_is_not_an_option_the_backend_declares():
    options = declared_options(get_backend("kripke-enum"), "modal")
    assert "timeout" not in options
    assert {"frame", "systems", "max_worlds", "max_atoms", "max_models"} <= options


def test_the_hybrid_decision_gives_both_halves_the_limit_of_its_call():
    # ¬PHP(6, 6) is not valid (six pigeons fit in six holes), so Z3 finds nothing to prove; the
    # enumeration then looks for a valuation of 36 atoms, and the first satisfying one in its order
    # is numbered about 2 ** 35: it is never reached, and only the limit ends the call.
    start = time.perf_counter()
    verdict = hybrid_down.down_decide(Not(_pigeonhole(6, 6)), timeout=1000)
    assert time.perf_counter() - start < 1.0 + SLACK
    assert verdict.status == UNKNOWN and verdict.reason == "timeout"
    assert "kripke-enum: timeout" in verdict.detail


def test_valuations_are_listed_once_per_world_count_when_few_and_generated_again_when_many(monkeypatch):
    # □p → ¬◇¬p is valid over K. With one atom the valuations of one world count are 2 (one world)
    # and 4 (two worlds), and the alethic relations over one world are 2 and over two worlds 16:
    # one listing per world count when the lists are kept, 2 + 16 when each relation choice
    # generates them again. The search itself is the same either way: 2 * 2 + 16 * 4 = 68 candidates.
    calls = []
    real = kripke_enum._valuations

    def spy(atoms, n, fixed=()):
        calls.append(n)
        return real(atoms, n, fixed)

    monkeypatch.setattr(kripke_enum, "_valuations", spy)
    kept = modal_enum_search(DUALITY, max_worlds=2)
    assert sorted(calls) == [1, 2] and kept.exhausted and kept.checked == 68
    calls.clear()
    monkeypatch.setattr(kripke_enum, "_CACHED_VALUATIONS", 0)
    again = modal_enum_search(DUALITY, max_worlds=2)
    assert sorted(calls) == [1] * 2 + [2] * 16
    assert again.to_dict() == kept.to_dict()


def test_the_valuations_of_many_atoms_are_generated_and_not_copied_into_memory():
    # 36 atoms are 2 ** 36 bitmasks for one world: far more than fits in memory as a list or a tuple,
    # and the first of them are produced at once, in the order of the integers
    stream = kripke_enum._valuations(tuple(f"a{i:02d}" for i in range(36)), 2)
    first = [next(stream) for _ in range(3)]
    assert first[0] == {0: frozenset(), 1: frozenset()}
    assert first[1] == {0: frozenset(), 1: frozenset({"a00"})}
    assert first[2] == {0: frozenset(), 1: frozenset({"a01"})}


def test_the_generated_bitmask_tuples_are_the_tuples_of_itertools_product_in_its_order():
    import itertools
    for count in (1, 2, 4):
        for n in (0, 1, 2, 3):
            assert list(kripke_enum._bitmask_tuples(count, n)) == list(itertools.product(range(count), repeat=n))
