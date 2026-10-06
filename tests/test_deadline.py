"""The wall-clock limit that the in-house searches share (``unicode_fol_kit._deadline``).

A search turns its limit in milliseconds into one instant of ``time.perf_counter()`` when the
call starts (:func:`instant`), asks whether it has passed (:func:`passed`) and how much is left
(:func:`remaining_ms`). A function that has no loop of its own to read a clock in is run under
:func:`run_until`, which ends it at the deadline from outside.

The workload is a function that builds a tree with ``2 ** 40`` leaves by recursion: it would
run for days, so only the deadline can end it, and what the tests measure is how long it took to
end.
"""

import threading
import time

import pytest

from unicode_fol_kit import _deadline

#: A call must end within its limit plus this much (the limits below are a few hundred
#: milliseconds, and the machine may be busy).
SLACK = 5.0


def _blow_up(depth):
    """A tree with ``2 ** depth`` leaves; for 40 more work than any limit here allows."""
    if depth == 0:
        return ("leaf",)
    return (_blow_up(depth - 1), _blow_up(depth - 1))


def test_no_limit_is_no_instant_and_never_passed():
    assert _deadline.instant(None) is None
    assert _deadline.passed(None) is False
    assert _deadline.remaining_ms(None) is None


def test_an_instant_in_the_future_has_not_passed_and_one_in_the_past_has():
    assert _deadline.passed(_deadline.instant(60_000)) is False
    assert _deadline.passed(_deadline.instant(-1)) is True


def test_what_is_left_of_a_limit_is_between_zero_and_the_limit():
    left = _deadline.remaining_ms(_deadline.instant(60_000))
    assert 50_000 < left <= 60_000
    assert _deadline.remaining_ms(_deadline.instant(-5)) == 0.0


def test_a_function_that_finishes_gives_its_value():
    assert _deadline.run_until(_deadline.instant(60_000), lambda: sum(range(1000))) == (True, 499500)


def test_without_a_limit_it_is_a_plain_call():
    assert _deadline.run_until(None, lambda: "value") == (True, "value")


def test_a_limit_that_has_passed_runs_nothing():
    ran = []
    assert _deadline.run_until(_deadline.instant(-1), lambda: ran.append(1)) == (False, None)
    assert ran == []


@pytest.mark.parametrize("limit_ms", [100, 400])
def test_a_function_that_has_no_end_is_cut_off_at_its_deadline(limit_ms):
    start = time.perf_counter()
    finished, value = _deadline.run_until(_deadline.instant(limit_ms), lambda: _blow_up(40))
    elapsed = time.perf_counter() - start
    assert (finished, value) == (False, None)
    assert elapsed >= limit_ms / 1000.0 * 0.9           # it did run until the deadline
    assert elapsed < limit_ms / 1000.0 + SLACK


def test_a_broad_handler_inside_the_function_does_not_swallow_the_cut_off():
    def swallowing():
        try:
            return _blow_up(40)
        except Exception:                                # the cut-off is not an ``Exception``
            return "swallowed"

    start = time.perf_counter()
    assert _deadline.run_until(_deadline.instant(200), swallowing) == (False, None)
    assert time.perf_counter() - start < 0.2 + SLACK


def test_an_exception_of_the_function_itself_propagates_unchanged():
    with pytest.raises(ZeroDivisionError):
        _deadline.run_until(_deadline.instant(60_000), lambda: 1 // 0)


def test_the_deadline_cuts_off_the_function_that_set_it_and_no_other():
    # an inner call with a short limit inside an outer one with a long limit: the inner call
    # ends, the outer function goes on and finishes
    start = time.perf_counter()
    finished, inner = _deadline.run_until(
        _deadline.instant(30_000),
        lambda: _deadline.run_until(_deadline.instant(150), lambda: _blow_up(40)))
    assert finished is True and inner == (False, None)
    assert time.perf_counter() - start < 0.15 + SLACK
    # an outer call with a short limit around an inner one with a long limit: the outer one ends
    start = time.perf_counter()
    finished, value = _deadline.run_until(
        _deadline.instant(150),
        lambda: _deadline.run_until(_deadline.instant(30_000), lambda: _blow_up(40)))
    assert (finished, value) == (False, None)
    assert time.perf_counter() - start < 0.15 + SLACK


def test_a_function_that_finished_in_time_is_never_interrupted_afterwards():
    # the timer of a finished call is cancelled and an exception it had scheduled is withdrawn:
    # a few hundred short calls, each with a deadline so close that the timer races the function,
    # and busy work after each of them, must not raise anywhere
    for size in range(300):
        _deadline.run_until(_deadline.instant(1), lambda: sum(range(200 + size * 5)))
        for _ in range(2000):
            pass
    deadline = time.perf_counter() + 0.3
    _deadline.run_until(_deadline.instant(50), lambda: None)
    while time.perf_counter() < deadline:               # the cancelled timer's instant passes
        sum(range(100))


def test_the_cut_off_works_when_called_from_another_thread():
    result = {}

    def work():
        start = time.perf_counter()
        result["answer"] = _deadline.run_until(_deadline.instant(150), lambda: _blow_up(40))
        result["elapsed"] = time.perf_counter() - start

    thread = threading.Thread(target=work)
    thread.start()
    thread.join(timeout=30)
    assert result["answer"] == (False, None)
    assert result["elapsed"] < 0.15 + SLACK


def test_an_interpreter_that_cannot_interrupt_a_thread_runs_the_function_to_its_end(monkeypatch):
    monkeypatch.setattr(_deadline, "_CAN_INTERRUPT", False)
    # the deadline has passed long before the function ends, and the function is not cut off
    assert _deadline.run_until(_deadline.instant(1), lambda: time.sleep(0.05) or "done") == (True, "done")
