"""A wall-clock limit shared by the kit's in-house searches.

Every in-house search (the classical and the labelled tableaux, resolution, the finite model
finder, the Kripke enumerator, the LTL tableau) takes its limit in milliseconds and turns it into
one instant on the ``time.perf_counter()`` clock when the call starts. This module holds the two
things they share.

* :class:`DeadlineReached` is what a search raises from deep inside its own loops to unwind to its
  entry point, which answers "no answer within the limit". It is raised by the search itself, at
  a place the search chose.

* :func:`run_until` runs a function that has no loop of its own to put a check in: it is the
  normal-form conversion that precedes a resolution search, or a routine of another module that
  the search only calls. It ends the call at the deadline by raising an exception in the calling
  thread (``PyThreadState_SetAsyncExc``), which Python delivers at the next bytecode, so a
  conversion that blows up exponentially is cut off within a few milliseconds of the deadline
  and costs nothing before it. A call into C code (a long ``itertools`` step, a solver) is not
  interrupted until it returns, and a function must be safe to abandon half-way: it may build
  data of its own but must not leave a shared structure half-written.

**When the interruption can arrive.** An asynchronous exception is delivered at whatever
bytecode the thread executes next, so the helper decides, for every instant of a call, whether
the timer may post one and where it would land.

* Before the call arms the timer nothing can be posted: the timer thread is started in a state
  in which it only notes that it ran out, and a call whose timer ran out first gives up without
  running the function.
* From the moment the call arms the timer until its own clean-up has withdrawn what the timer
  may have left, every bytecode of the thread lies inside the one ``try`` statement that catches
  this call's own exception class: the function, the instants between its return and the
  clean-up, and the clean-up itself.
* The clean-up is one critical section: it ends the timer's right to post and takes back an
  exception that was posted but not yet delivered. After it, nothing of this call is pending,
  and what runs next (the handler, the caller's code) is never interrupted by this call.
* The clean-up is repeated by an outer ``finally``, so another exception that cuts the first
  one short (a ``KeyboardInterrupt``, the cut-off of an enclosing call) cannot leave the timer
  armed.
* Calls in different threads do not meet: each call has its own timer, its own lock and its own
  exception class, and the exception is posted to the thread that made the call.

Two things the helper cannot do. A thread has room for ONE pending asynchronous exception, so
of two nested limits that expire within the same few microseconds only one is delivered, and
the enclosing call may miss its own limit and run on to its end; it is never interrupted at a
place where nothing is waiting for it. And Python prints and drops an exception that is raised
inside a ``__del__`` or a weak-reference callback, so a function that happens to run one at the
very instant the exception lands is not cut off (the call then ends late, with its own answer).
"""

import threading
import time
from typing import Any, Callable, Optional, Tuple, Type, TypeVar

try:
    import ctypes
    _SET_ASYNC_EXC: Optional[Any] = ctypes.pythonapi.PyThreadState_SetAsyncExc
except Exception:                       # an interpreter without ctypes, or without the C API through it
    ctypes = None                       # type: ignore[assignment]
    _SET_ASYNC_EXC = None

__all__ = ["DeadlineReached", "instant", "passed", "remaining_ms", "run_until"]

T = TypeVar("T")


class DeadlineReached(Exception):
    """A search ran past its deadline (raised by the search, caught at its entry point)."""


def instant(timeout_ms: Optional[float]) -> Optional[float]:
    """The ``perf_counter`` instant ``timeout_ms`` milliseconds from now; ``None`` for no limit."""
    return None if timeout_ms is None else time.perf_counter() + timeout_ms / 1000.0


def passed(deadline: Optional[float]) -> bool:
    """True iff ``deadline`` (an instant from :func:`instant`) is in the past; never for ``None``."""
    return deadline is not None and time.perf_counter() > deadline


def remaining_ms(deadline: Optional[float]) -> Optional[float]:
    """The milliseconds left until ``deadline`` (not below 0), or ``None`` for no limit."""
    if deadline is None:
        return None
    return max(0.0, (deadline - time.perf_counter()) * 1000.0)


class _Interrupted(BaseException):
    """Delivered into the calling thread at the deadline by :func:`run_until`.

    A ``BaseException``, so that a broad ``except Exception`` somewhere in the interrupted code
    cannot swallow it; :func:`run_until` is the only place that catches it.
    """


#: Whether this interpreter can raise an exception in a running thread (CPython can).
_CAN_INTERRUPT = _SET_ASYNC_EXC is not None


def _set_async_exception(thread_id: int, exception: Optional[type]) -> int:
    """Ask the interpreter to raise ``exception`` in thread ``thread_id`` (``None`` clears a pending one)."""
    assert _SET_ASYNC_EXC is not None
    return _SET_ASYNC_EXC(ctypes.c_ulong(thread_id), ctypes.py_object(exception) if exception else None)


#: The states of a :class:`_Cutoff`.
_IDLE = 0       # the function has not begun: a timer that runs out now only notes it
_ARMED = 1      # the function runs under the limit: a timer that runs out now posts
_POSTED = 2     # the interruption was posted: delivered by now, or still pending
_EXPIRED = 3    # the timer ran out before the function began: the function must not run
_DONE = 4       # the call is over: the timer has no right left


class _Cutoff:
    """What the calling thread and the timer thread of one :func:`run_until` call share.

    A state that only changes under one lock, so that the two never disagree about whether an
    interruption has been posted:

    * ``_IDLE`` → ``_ARMED`` when the calling thread is about to run the function (:meth:`arm`);
    * ``_ARMED`` → ``_POSTED`` when the timer runs out and posts the interruption to the thread
      (:meth:`fire`);
    * ``_IDLE`` → ``_EXPIRED`` when the timer runs out first, which tells :meth:`arm` that the
      limit is over already (nothing is posted: the thread is not inside the guarded region);
    * any state → ``_DONE`` on :meth:`disarm`, which withdraws a posted interruption that was not
      delivered yet.

    Every call has its own exception class, so a nested call is cut off by its own timer and by
    no other.

    The timer itself is NOT a field. A timer that this object also pointed back to would make a
    reference cycle, and a cycle's garbage is collected whenever the collector next runs: its
    clean-up (a weak-reference callback of the ``threading`` module that drops the finished timer
    thread) would then run in the middle of some later call's function, and an exception
    delivered into such a callback is printed and dropped, which loses that call's cut-off.
    Without the cycle the timer thread's object dies, by its reference count, when
    :func:`run_until` returns.
    """

    __slots__ = ("thread_id", "interrupt", "_lock", "_state")

    def __init__(self) -> None:
        self.thread_id = threading.get_ident()
        self.interrupt: Type[BaseException] = type("_Interrupted", (_Interrupted,), {})
        self._lock = threading.Lock()
        self._state = _IDLE

    def fire(self) -> None:
        """Run on the timer thread when the limit is over."""
        with self._lock:
            if self._state == _ARMED:
                self._state = _POSTED
                _set_async_exception(self.thread_id, self.interrupt)
            elif self._state == _IDLE:
                self._state = _EXPIRED

    def arm(self) -> bool:
        """Let the timer post from now on; False if its limit is over already (run nothing)."""
        with self._lock:
            if self._state != _IDLE:
                return False
            self._state = _ARMED
            return True

    def disarm(self) -> None:
        """End the timer's right to post, and take back an interruption it posted and left pending.

        Idempotent, so that a second call can complete a first one that another exception cut
        short: a state that is not ``_DONE`` yet says what is left to do.
        """
        with self._lock:                                # a timer that is posting has finished by now
            if self._state == _POSTED:
                _set_async_exception(self.thread_id, None)
            self._state = _DONE


def run_until(deadline: Optional[float], function: Callable[[], T]) -> Tuple[bool, Optional[T]]:
    """Run ``function()``; return ``(True, value)``, or ``(False, None)`` if it was cut off at ``deadline``.

    ``deadline`` is an instant from :func:`instant`; ``None`` means no limit, and then this is a
    plain call. A deadline that has passed already runs nothing, and so does one that passes
    while the call is being set up (the answer is ``(False, None)`` either way). When the
    deadline passes while ``function`` is still running, an exception is raised in this thread
    at the next bytecode and ends it: the result is ``(False, None)`` and nothing the function
    built is returned. An interruption that arrives after the function returned, or inside the
    clean-up of this call, is absorbed: the result is then ``(False, None)`` if it cut the
    return short and ``(True, value)`` if the function had finished. Nothing of this call is
    ever raised into the caller, whatever the limit and however many threads call at once. A
    function that finishes first costs one timer thread and nothing else. Nested calls are
    independent: each cuts off only its own function (see the module docstring for the one
    case in which an enclosing call can be late). On an interpreter that cannot raise an
    exception in a running thread the function simply runs to its end.

    ``function`` must be safe to abandon half-way (see the module docstring), and must not catch
    ``BaseException``. An exception that ``function`` raises on its own propagates unchanged.
    """
    if deadline is None or not _CAN_INTERRUPT:
        return True, function()
    if passed(deadline):
        return False, None
    cutoff = _Cutoff()
    timer = threading.Timer(max(0.0, deadline - time.perf_counter()), cutoff.fire)
    timer.daemon = True
    value: Optional[T] = None
    finished = False
    try:
        try:
            try:
                timer.start()                           # cannot post yet: the call is not armed
                if cutoff.arm():
                    value = function()
                    finished = True
            finally:
                cutoff.disarm()
                timer.cancel()
        except cutoff.interrupt:
            pass
    finally:
        cutoff.disarm()                                 # again: finishes a clean-up that was cut short
        timer.cancel()
    return finished, (value if finished else None)
