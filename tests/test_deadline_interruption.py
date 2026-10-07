r"""``run_until`` never lets its own interruption leave the call, at any limit and from any thread.

``run_until(deadline, function)`` ends ``function`` at the deadline by raising an exception in the calling
thread. That exception is a ``BaseException``, so no ``except Exception`` of a caller stops it: if it ever
arrives where nothing of the call is waiting for it, it ends whatever the thread runs next. The call is
therefore built so that no instant exists at which it can land outside the call:

* before the function begins, the timer cannot post: a timer that runs out while it is being set up only
  makes the call give up (``(False, None)``, the function not run);
* while the function runs, and in the instants between its return and the clean-up, and in the clean-up,
  the exception lands inside the one ``try`` that catches it;
* the clean-up ends the timer's right to post and takes back an exception that was posted and is still
  pending, as one step, and is repeated if another exception cuts it short.

The first tests pin each of these on their own, with a timer that runs out at a chosen instant (the timer of
the module is ``threading.Timer``, replaced here by one whose ``start`` or ``cancel`` runs the function the
timer would run: the instant is then exact, not a matter of timing). The next ones replace the call into the
interpreter that posts the exception by one that records and delivers nothing, to see what is posted and what
is taken back. The last ones drive the real timers at limits from a microsecond to twenty milliseconds, from
one thread and from three, against functions that finish at about the limit, and then wait: everything a
call returns is ``(True, value)`` with the value of the function, or ``(False, None)``; nothing is raised,
then or later; and the ordinary calls between them answer as they do in a fresh process (the answers are the
hand-derived ones of the module).
"""

import collections
import gc
import threading
import time

import pytest

from unicode_logic_kit import _deadline
from unicode_logic_kit._deadline import instant, run_until

#: Limits in milliseconds, from far below what starting a thread takes to a few times it.
LIMITS_MS = (0.001, 0.003, 0.01, 0.05, 0.2, 0.5, 1, 2, 5, 20)
#: Sizes of the functions that finish: ``sum(range(size))`` takes from nothing to some milliseconds.
SIZES = (0, 10, 1_000, 20_000, 200_000)


def _wait(seconds):
    """Run bytecode for ``seconds``, so that an exception left pending would be delivered."""
    end = time.perf_counter() + seconds
    while time.perf_counter() < end:
        sum(range(100))


class _TimerThatRunsOutAt:
    """A stand-in for ``threading.Timer`` that runs its function at a chosen instant, in the thread
    that calls it: ``"start"`` (the limit is over while the timer is being started) or ``"cancel"``
    (while the call is cancelling it), or never (the test calls ``trigger`` itself)."""

    instant = None
    last = None

    def __init__(self, interval, function):
        self.function = function
        self.daemon = False
        self.cancelled = 0
        _TimerThatRunsOutAt.last = self

    def start(self):
        if _TimerThatRunsOutAt.instant == "start":
            self.function()

    def cancel(self):
        self.cancelled += 1
        if _TimerThatRunsOutAt.instant == "cancel":
            self.function()

    def trigger(self):
        self.function()


@pytest.fixture
def fake_timer(monkeypatch):
    monkeypatch.setattr(_deadline.threading, "Timer", _TimerThatRunsOutAt)
    _TimerThatRunsOutAt.instant = None
    _TimerThatRunsOutAt.last = None
    yield _TimerThatRunsOutAt
    _TimerThatRunsOutAt.instant = None


# ---------------------------------------------------------------------------------------------
# each instant on its own
# ---------------------------------------------------------------------------------------------
def test_a_limit_that_is_over_while_the_timer_is_set_up_runs_nothing_and_raises_nothing(fake_timer):
    # the timer runs out inside ``start``, before the call has begun to run the function
    fake_timer.instant = "start"
    ran = []
    assert run_until(instant(60_000), lambda: ran.append(1)) == (False, None)
    assert ran == []
    _wait(0.05)                                    # nothing was left pending


def test_a_timer_that_runs_out_inside_the_function_cuts_it_off(fake_timer):
    def endless():
        fake_timer.last.trigger()                  # the limit is over now, in the middle of the function
        while True:
            pass

    start = time.perf_counter()
    assert run_until(instant(60_000), endless) == (False, None)
    assert time.perf_counter() - start < 5
    _wait(0.05)


def test_a_timer_that_runs_out_while_the_call_cleans_up_changes_nothing(fake_timer):
    # the function has returned; the timer runs out as the call cancels it
    fake_timer.instant = "cancel"
    assert run_until(instant(60_000), lambda: "value") == (True, "value")
    assert fake_timer.last.cancelled >= 1
    _wait(0.05)


def test_a_timer_that_runs_out_after_the_call_is_over_posts_nothing(fake_timer):
    assert run_until(instant(60_000), lambda: "value") == (True, "value")
    fake_timer.last.trigger()                      # the timer thread that was past its check when the call ended
    _wait(0.05)                                    # an exception that was posted would land here


def test_an_exception_that_cuts_the_clean_up_short_does_not_leave_the_call_armed(fake_timer, monkeypatch):
    # another exception (a KeyboardInterrupt) arrives in the clean-up, in ``cancel``
    calls = []

    def cancel_once_interrupted(self):
        calls.append(1)
        if len(calls) == 1:
            raise KeyboardInterrupt

    monkeypatch.setattr(fake_timer, "cancel", cancel_once_interrupted)
    with pytest.raises(KeyboardInterrupt):
        run_until(instant(60_000), lambda: "value")
    assert len(calls) >= 2                         # the clean-up was run again
    fake_timer.last.trigger()                      # the timer runs out after all: it has no right left
    _wait(0.05)


def test_the_function_that_raised_on_its_own_still_ends_the_timer(fake_timer):
    with pytest.raises(ZeroDivisionError):
        run_until(instant(60_000), lambda: 1 // 0)
    assert fake_timer.last.cancelled >= 1
    fake_timer.last.trigger()
    _wait(0.05)


# ---------------------------------------------------------------------------------------------
# what is posted and what is taken back (the poster is replaced by one that records and delivers nothing)
# ---------------------------------------------------------------------------------------------
@pytest.fixture
def posts(monkeypatch):
    """The calls the module makes to the interpreter's ``PyThreadState_SetAsyncExc``, in order: the exception
    class that is posted, or ``None`` for a withdrawal. Nothing is delivered, so an exception that is posted
    stays pending, as it does when the thread runs no bytecode between the post and the clean-up."""
    calls = []
    monkeypatch.setattr(_deadline, "_set_async_exception",
                        lambda thread_id, exception: calls.append(exception) or 1)
    return calls


def test_an_exception_that_was_posted_and_not_delivered_is_taken_back(fake_timer, posts):
    assert run_until(instant(60_000), lambda: fake_timer.last.trigger() or "value") == (True, "value")
    assert len(posts) == 2
    assert issubclass(posts[0], BaseException) and posts[1] is None


def test_a_call_whose_timer_posted_nothing_takes_nothing_back(fake_timer, posts):
    # an exception that is pending for someone else (an enclosing call, another library) is not this call's
    assert run_until(instant(60_000), lambda: "value") == (True, "value")
    assert posts == []
    fake_timer.last.trigger()                      # the timer runs out after the call: it has no right left
    assert posts == []


def test_a_timer_that_runs_out_before_the_function_begins_posts_nothing(fake_timer, posts):
    fake_timer.instant = "start"
    assert run_until(instant(60_000), lambda: "value") == (False, None)
    assert posts == []


def test_each_call_posts_an_exception_class_of_its_own(fake_timer, posts):
    classes = []
    for _ in range(2):
        run_until(instant(60_000), lambda: fake_timer.last.trigger())
        classes.append(posts[-2])
    assert classes[0] is not classes[1]
    assert issubclass(classes[0], BaseException) and issubclass(classes[1], BaseException)


# ---------------------------------------------------------------------------------------------
# the real timers
# ---------------------------------------------------------------------------------------------
def _endless():
    while True:
        pass


#: ordinary calls, run with a limit no machine reaches, and what they answer (derived by hand)
def _ordinary_calls():
    from unicode_logic_kit.atp import resolution
    from unicode_logic_kit.atp.logic_backends import IntBackend
    from unicode_logic_kit.fol.nodes import Atom, Constant, Implies, Not, Or, Quantifier, Variable

    x, alpha = Variable("x"), Constant("alpha")
    p = Atom("p", [])
    all_p_q = Quantifier("∀", x, Implies(Atom("P", [x]), Atom("Q", [x])))
    return [
        # modus ponens: ∀x (P(x) → Q(x)), P(α) ⊢ Q(α)
        (lambda: resolution.prove([all_p_q, Atom("P", [alpha])], Atom("Q", [alpha]), timeout=60_000), True),
        # P(α) ⊬ Q(α): P = {α}, Q = {}
        (lambda: resolution.prove([Atom("P", [alpha])], Atom("Q", [alpha]), timeout=60_000), False),
        # p → p is a theorem
        (lambda: IntBackend().decide(Implies(p, p), [], timeout=60_000).status, "proved"),
        # p ∨ ¬p is not intuitionistically valid (the root holds no atom, its one successor holds p)
        (lambda: IntBackend().decide(Or(p, Not(p)), [], timeout=60_000).status, "refuted"),
    ]


def _one_call(index, ordinary):
    """One call with a limit and a function chosen by ``index``; None if it is as it must be, else
    what is wrong. Every ninth call is a function with no end, every thirty-third an ordinary call."""
    if index % 33 == 7:
        call, expected = ordinary[(index // 33) % len(ordinary)]
        got = call()
        return None if got == expected else f"ordinary call {index // 33 % len(ordinary)}: {got!r} != {expected!r}"
    limit = LIMITS_MS[index % len(LIMITS_MS)]
    if index % 9 == 4:
        limit = (2, 5, 20)[index % 3]
        got = run_until(instant(limit), _endless)
        return None if got == (False, None) else f"endless function, limit {limit} ms: {got!r}"
    size = SIZES[(index // 3) % len(SIZES)]
    got = run_until(instant(limit), lambda: sum(range(size)))
    wanted = size * (size - 1) // 2
    return None if got in ((True, wanted), (False, None)) else f"limit {limit} ms, size {size}: {got!r}"


def _drive(first, count, ordinary, problems):
    """``count`` calls from ``first``; anything raised or wrong, and anything that arrives after, goes to ``problems``."""
    try:
        for index in range(first, first + count):
            try:
                wrong = _one_call(index, ordinary)
            except BaseException as exc:           # noqa: BLE001 -- the point is that nothing leaves
                wrong = f"call {index} raised {type(exc).__module__}.{type(exc).__name__}"
            if wrong:
                problems.append(wrong)
        _wait(0.05)                                # whatever was left pending would land here
    except BaseException as exc:                   # noqa: BLE001
        problems.append(f"after the calls: {type(exc).__module__}.{type(exc).__name__}")


def test_limits_from_a_microsecond_to_twenty_milliseconds_raise_nothing_in_one_thread():
    problems = []
    ordinary = _ordinary_calls()
    _drive(0, 700, ordinary, problems)
    assert problems == [], collections.Counter(problems).most_common(5)


def test_the_same_calls_from_three_threads_at_once_raise_nothing():
    problems = []
    ordinary = _ordinary_calls()
    threads = [threading.Thread(target=_drive, args=(1000 * (k + 1), 300, ordinary, problems))
               for k in range(3)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(timeout=120)
        assert not thread.is_alive()
    _wait(0.1)
    assert problems == [], collections.Counter(problems).most_common(5)


def test_the_answers_after_the_stress_are_the_answers_of_a_fresh_process():
    # a call that ran into a limit leaves nothing behind that changes a later one
    for index in range(100):
        run_until(instant(LIMITS_MS[index % len(LIMITS_MS)]), lambda: sum(range(5_000)))
    for call, expected in _ordinary_calls():
        assert call() == expected


def test_a_finished_call_leaves_no_timer_thread_to_the_cycle_collector():
    # A timer thread that stayed in a reference cycle would be dropped by the collector in the middle of
    # a later call, by a weak-reference callback of ``threading``; an exception delivered there is
    # printed and dropped, and that call's cut-off is lost.
    gc.collect()
    previous = gc.get_debug()
    gc.set_debug(gc.DEBUG_SAVEALL)
    try:
        for _ in range(60):
            run_until(instant(50), lambda: None)
        gc.collect()
        leftovers = [o for o in gc.garbage if isinstance(o, threading.Thread)]
    finally:
        gc.set_debug(previous)
        del gc.garbage[:]
    assert leftovers == []
