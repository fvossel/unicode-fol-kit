r"""The intuitionistic and the relevant backend end at the limit of the call.

A backend that searches for something exponential in its input takes its limit in milliseconds and
answers ``unknown`` with the reason ``timeout`` when the search has not finished by then. Three searches of
the two backends are under the limit, and each has an input that no limit of a second or less can wait for:

* ``IntBackend``, the proof search (``int_prove``). The chain ``f0 = p0``, ``fk = ((f(k-1) → pk) → f(k-1))``
  (Peirce's law nested) gives the search of G4ip more than 200 000 steps from ``k = 7`` on, about a second and
  a half on the machine that measured it. A call with a limit of 100 ms must say ``unknown`` / ``timeout``:
  it is not an answer of the search that was not given, and it is no ``refuted``.
* ``IntBackend``, the search for a countermodel of a refuted formula. ``(p0 → p1) ∨ (p1 → p2) ∨ … ∨
  (p13 → p0)`` is not intuitionistically valid: a root world that holds no atom, with one successor ``ui`` per
  ``i`` that holds ``pi`` and nothing else, refutes every disjunct (at ``ui``, ``pi`` holds and ``p(i+1)``
  does not). So the verdict is ``refuted`` at once, from the proof search, and the witness search, which
  tries structures of up to three worlds where the smallest countermodel has fifteen, has nothing to find and
  nothing to end it but the limit. The verdict stays ``refuted``, without a witness.
* ``RelevantBackend``. ``(p0 ∧ … ∧ p11) → p0`` is a theorem of B (conjunction elimination), the backend
  never answers ``proved``, and the search for a countermodel it runs is exponential in the twelve atoms: a
  limit of a second ends it with ``unknown`` / ``timeout``, not ``bound_hit``.

The two searches that nothing but the limit can end are run in a child process with a hard kill, so that a
backend without its limit makes the test fail instead of making it wait.
"""

import json
import os
import subprocess
import sys
import time

import unicode_logic_kit
from unicode_logic_kit.atp.logic_backends import IntBackend
from unicode_logic_kit.fol.nodes import And, Atom, Implies, Not, Or

#: A call must end within its limit plus this much of the limit (and at least five seconds:
#: a busy runner was measured 1.2 s past a limit of 0.3 s).
SLACK_FRACTION = 0.25
SLACK_MINIMUM = 5.0
#: What a child process may take in all, import of the package included, before it is killed.
HARD_LIMIT = 40

_CHILD = '''
import json
import time

from unicode_logic_kit.atp.logic_backends import IntBackend, RelevantBackend
from unicode_logic_kit.fol.nodes import And, Atom, Implies, Or


def atom(name):
    return Atom(name, [])


def cycle(n):
    parts = [Implies(atom("p%d" % i), atom("p%d" % ((i + 1) % n))) for i in range(n)]
    out = parts[0]
    for part in parts[1:]:
        out = Or(out, part)
    return out


def conjunction(names):
    out = atom(names[0])
    for name in names[1:]:
        out = And(out, atom(name))
    return out


if KIND == "int-witness":
    backend, formula, premises = IntBackend(), cycle(14), []
else:
    backend = RelevantBackend()
    formula, premises = atom("p0"), [conjunction(["p%d" % i for i in range(12)])]
start = time.perf_counter()
verdict = backend.decide(formula, premises, timeout=LIMIT)
print(json.dumps({"status": verdict.status, "reason": verdict.reason,
                  "witness": verdict.countermodel is not None,
                  "elapsed": time.perf_counter() - start}))
'''


def _in_child(kind, limit_ms):
    """The verdict of ``kind`` under ``limit_ms`` in a child process, as a dict (and its wall time)."""
    root = os.path.dirname(os.path.dirname(os.path.abspath(unicode_logic_kit.__file__)))
    env = dict(os.environ, PYTHONIOENCODING="utf-8", PYTHONDONTWRITEBYTECODE="1",
               PYTHONPATH=os.pathsep.join([root] + [p for p in os.environ.get("PYTHONPATH", "").split(os.pathsep) if p]))
    code = _CHILD.replace("KIND", repr(kind)).replace("LIMIT", str(limit_ms))
    done = subprocess.run([sys.executable, "-c", code], env=env, capture_output=True, text=True,
                          encoding="utf-8", timeout=HARD_LIMIT)
    assert done.returncode == 0, done.stderr[-2000:]
    return json.loads(done.stdout.strip().splitlines()[-1])


def _within(elapsed, limit_ms):
    return elapsed < limit_ms / 1000.0 + max(SLACK_MINIMUM, SLACK_FRACTION * limit_ms / 1000.0)


def _nested_peirce(depth):
    """``f0 = p0``, ``fk = ((f(k-1) → pk) → f(k-1))``."""
    formula = Atom("p0", [])
    for k in range(1, depth + 1):
        formula = Implies(Implies(formula, Atom(f"p{k}", [])), formula)
    return formula


def test_the_proof_search_ends_at_the_limit_with_no_verdict():
    # Depth 6: the search runs for about a second and stays a few hundred frames deep, so the
    # limit is the only bound it can meet (from depth 8 on it also outgrows the interpreter's
    # recursion limit, and which of the two bounds comes first is a race).
    start = time.perf_counter()
    verdict = IntBackend().decide(_nested_peirce(6), [], timeout=100)
    elapsed = time.perf_counter() - start
    assert (verdict.status, verdict.reason) == ("unknown", "timeout")
    assert verdict.countermodel is None
    assert _within(elapsed, 100), elapsed


def test_the_witness_search_ends_at_the_limit_and_the_refutation_stays():
    # no witness exists within three worlds: the search can only be ended by the limit
    result = _in_child("int-witness", 1000)
    assert result["status"] == "refuted"
    assert result["witness"] is False
    assert _within(result["elapsed"], 1000), result


def test_the_relevant_search_ends_at_the_limit_with_no_verdict():
    result = _in_child("relevant", 1000)
    assert (result["status"], result["reason"]) == ("unknown", "timeout")
    assert result["witness"] is False
    assert _within(result["elapsed"], 1000), result


def test_a_search_that_finishes_in_time_answers_as_it_did_without_a_limit():
    p = Atom("p", [])
    # p → p is a theorem
    assert IntBackend().decide(Implies(p, p), [], timeout=60_000).status == "proved"
    # p ∨ ¬p is not: the root holds nothing, its one successor holds p, so neither p nor ¬p holds at the
    # root; the witness search finds that model within three worlds
    refuted = IntBackend().decide(Or(p, Not(p)), [], timeout=60_000)
    assert refuted.status == "refuted"
    assert refuted.countermodel is not None and refuted.countermodel["kind"] == "intuitionistic_kripke"
    # (p ∧ q) → p is a theorem of intuitionistic logic; the relevant backend never answers "proved"
    from unicode_logic_kit.atp.logic_backends import RelevantBackend
    q = Atom("q", [])
    small = RelevantBackend().decide(p, [And(p, q)], timeout=60_000)
    assert small.status == "unknown" and small.reason == "bound_hit"
