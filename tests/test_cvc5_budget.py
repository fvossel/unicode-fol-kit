"""The cvc5 backend honours its time budget.

``Cvc5Backend`` used to set only cvc5's ``tlimit``. On a problem whose
quantifier instantiation never ends, that option did not stop the check at all
(measured with cvc5 1.3.4: a 3000 ms ``tlimit`` and a 60 s hard cap, and the cap
fired), so the DEFAULT prover chain (z3, cvc5, ...) -- which runs cvc5 whenever
the package is installed -- never returned. ``tlimit-per``, the limit of ONE
query, which is exactly what the backend asks, does stop it: ``unknown`` with
the explanation ``TIMEOUT`` after 3.09 s for a 3000 ms budget.

The problem is the description-logic image of a one-GCI knowledge base in the
two-sorted regime, written out by hand so the test does not depend on the DL
layer:

* GCI, relativised to the object sort: every ``OwlThing`` has an ``R``-successor
  that is a ``C`` (``∀x (OwlThing(x) → ∃y (R(x, y) ∧ C(y)))``);
* ``R`` is typed: both ends of an ``R``-edge are ``OwlThing``;
* goal: ``∀x (OwlThing(x) → x ≠ x)`` -- "no thing exists".

Hand-derived: the premises do NOT entail the goal. The structure with one
element ``a``, ``OwlThing(a)``, ``R(a, a)``, ``C(a)`` satisfies both premises and
falsifies the goal. So PROVED would be wrong; the honest answers are UNKNOWN
(budget spent) or REFUTED (the model found); what must never happen is no answer.

Each problem runs in its own child process under a hard wall-clock cap, so a
regression makes THIS test fail instead of hanging the suite. The budget is never
shrunk to make the test fast: 3000 ms is the budget used here, and the
backend must come back within about twice that.
"""

import json
import subprocess
import sys
import textwrap

import pytest

pytest.importorskip("cvc5")

BUDGET_MS = 3000
#: What a machine that runs several test workers at once may add to a call. The
#: bound below was exactly twice the budget, and a loaded machine measured 6.14 s
#: against 6.0 s for a backend that had stopped on time. The slack is the one the
#: deadline tests of the in-house searches use; a backend that ignores its budget
#: runs into the hard cap, which is a minute later, so the test still tells the
#: two apart.
SLACK_S = 5.0
#: "within about twice the budget": the backend's own wall time for the call.
WALL_LIMIT_S = 2 * BUDGET_MS / 1000 + SLACK_S
#: What the CHILD may take in all (interpreter start, imports, translation, the
#: check). A cvc5 that ignores its budget is cut off here and the test fails.
HARD_CAP_S = 120

_CHILD_PRELUDE = f"""
import json
from unicode_logic_kit.atp.protocol import get_backend

def report(goal, premises):
    verdict = get_backend("cvc5").decide(goal, premises, timeout={BUDGET_MS})
    print("VERDICT " + json.dumps({{
        "status": verdict.status, "reason": verdict.reason,
        "wall": verdict.wall_time}}), flush=True)
"""

_HAND_WRITTEN = _CHILD_PRELUDE + textwrap.dedent("""
    from unicode_logic_kit import MSFLParser
    parse = MSFLParser().parse
    report(
        parse("∀x (OwlThing(x) → ¬x = x)"),
        [parse("∀x (OwlThing(x) → ∃y (R(x, y) ∧ C(y)))"),
         parse("∀x ∀y (R(x, y) → (OwlThing(x) ∧ OwlThing(y)))")])
""")

#: The same problem as it arises through the DL layer: the data layer makes the
#: image two-sorted, ``Top ⊔ Top ⊑ ∃r.C`` is the one GCI.
_THROUGH_THE_DL_LAYER = _CHILD_PRELUDE + textwrap.dedent("""
    import unicode_logic_kit.dl as dl
    tbox = dl.TBox().add(dl.Or(dl.Top(), dl.Top()), dl.Exists("r", dl.Atomic("C")))
    tbox.add_data_property_range("Z", dl.Datatype("xsd:integer"))
    kb = dl.kb_to_fol(tbox)
    report(dl.subsumption_to_fol(dl.Top(), dl.Not(dl.Top()), object_sort=True),
           list(kb.tbox_premises))
""")


def _run_in_child(script: str) -> dict:
    try:
        done = subprocess.run([sys.executable, "-c", script], capture_output=True,
                              text=True, timeout=HARD_CAP_S)
    except subprocess.TimeoutExpired:
        pytest.fail(f"cvc5 did not return within {HARD_CAP_S} s for a {BUDGET_MS} ms "
                    f"budget: the backend does not honour its time limit")
    lines = [ln for ln in done.stdout.splitlines() if ln.startswith("VERDICT ")]
    assert lines, f"the child printed no verdict:\n{done.stdout}\n{done.stderr[-2000:]}"
    return json.loads(lines[-1][len("VERDICT "):])


@pytest.mark.parametrize("script", [_HAND_WRITTEN, _THROUGH_THE_DL_LAYER],
                         ids=["hand-written", "through-the-dl-layer"])
def test_cvc5_returns_within_about_twice_its_budget_on_a_non_terminating_instantiation(script):
    verdict = _run_in_child(script)
    # The premises do not entail the goal (a one-element model refutes it), so a
    # proof would be a wrong answer; unknown/timeout is the honest one.
    assert verdict["status"] != "proved", verdict
    if verdict["status"] == "unknown":
        assert verdict["reason"] == "timeout", verdict
    assert verdict["wall"] <= WALL_LIMIT_S, (
        f"cvc5 took {verdict['wall']:.2f} s for a {BUDGET_MS} ms budget "
        f"(limit {WALL_LIMIT_S:.1f} s): {verdict}")


def test_cvc5_still_decides_an_ordinary_problem_with_the_per_query_limit_set():
    # The control: the budget is a limit, not a verdict. A problem cvc5 settles
    # at once is settled -- proved, with the budget never reached.
    from unicode_logic_kit import MSFLParser
    from unicode_logic_kit.atp.protocol import get_backend
    parse = MSFLParser().parse
    modus_ponens = get_backend("cvc5").decide(
        parse("Mortal(socrates)"),
        [parse("∀x (Human(x) → Mortal(x))"), parse("Human(socrates)")],
        timeout=BUDGET_MS)
    assert modus_ponens.status == "proved", modus_ponens
    # ... and a ground non-consequence is REFUTED with a countermodel, as before
    # (hand-derived: Human(socrates) true and Mortal(socrates) false satisfies the
    # premise and falsifies the goal).
    not_entailed = get_backend("cvc5").decide(
        parse("Mortal(socrates)"), [parse("Human(socrates)")], timeout=BUDGET_MS)
    assert not_entailed.status == "refuted", not_entailed
