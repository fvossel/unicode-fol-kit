"""The time of cvc5's proof child process is part of ``Verdict.wall_time``.

With ``proof=True`` the verdict is built from the main solve, and the Alethe text comes from a second solver
run in a child interpreter. A caller who asks for the proof waits for that run, and ``wall_time`` is what the
call took: it holds both. ``∀x (P(x) → Q(x)), P(a) ⊢ Q(a)`` is valid (one instantiation, modus ponens), so the
verdict is PROVED and the proof run is made.
"""
import time

import pytest

pytest.importorskip("cvc5")

from unicode_fol_kit import api
from unicode_fol_kit.atp import cvc5_backend
from unicode_fol_kit.atp.cvc5_backend import Cvc5Backend

PREMISES = [api.parse_any("∀x (P(x) → Q(x))").formula, api.parse_any("P(a)").formula]
GOAL = api.parse_any("Q(a)").formula


def _decide(**options):
    return Cvc5Backend().decide(GOAL, PREMISES, timeout=20000, **options)


def test_the_time_of_the_proof_run_is_part_of_the_wall_time(monkeypatch):
    def slow(*args, **kwargs):
        time.sleep(0.4)
        return "(proof text)", None
    monkeypatch.setattr(cvc5_backend, "_alethe_text", slow)
    verdict = _decide(proof=True)
    assert verdict.status == "proved" and verdict.proof["text"] == "(proof text)"
    assert verdict.wall_time >= 0.4                    # a lower bound: the sleep alone takes that long


def test_the_time_of_a_proof_run_that_gives_no_text_is_counted_too(monkeypatch):
    def slow_failure(*args, **kwargs):
        time.sleep(0.4)
        return None, "the proof run could not be started"
    monkeypatch.setattr(cvc5_backend, "_alethe_text", slow_failure)
    verdict = _decide(proof=True)
    assert verdict.status == "proved" and verdict.proof["text"] is None
    assert verdict.wall_time >= 0.4


def test_without_a_proof_request_no_proof_run_is_made_and_nothing_is_added(monkeypatch):
    calls = []

    def recorded(*args, **kwargs):
        calls.append(args)
        return "(proof text)", None
    monkeypatch.setattr(cvc5_backend, "_alethe_text", recorded)
    verdict = _decide()
    assert verdict.status == "proved" and calls == []


def test_a_real_proof_run_is_inside_the_wall_time(monkeypatch):
    real = cvc5_backend._alethe_text
    seconds = []

    def timed(*args, **kwargs):
        start = time.perf_counter()
        try:
            return real(*args, **kwargs)
        finally:
            seconds.append(time.perf_counter() - start)
    monkeypatch.setattr(cvc5_backend, "_alethe_text", timed)
    verdict = _decide(proof=True)
    assert verdict.status == "proved" and len(seconds) == 1
    assert verdict.wall_time >= seconds[0]
