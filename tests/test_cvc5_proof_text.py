"""cvc5's Alethe proof text is opt-in, and produced by a child process.

cvc5 1.3.4's proof PRINTER (``Solver.proofToString``) can end the calling process with a native access
violation: ``∀x f(carl) = x ⊢ ∃w ∀x f(carl) = x`` does, while ``checkSat``, ``getProof`` and
``getUnsatCore`` on the same solver are fine. A native crash is not a Python exception, so no ``try`` around
the call can protect the caller; a backend that printed the proof of every PROVED verdict would end the Python
process on ``api.prove(backends=["cvc5"])`` for that problem.

So the default path asks for neither a proof nor its text (the unsat core does not need one), and the text is
produced only on request, ``decide(..., proof=True)``, by a SECOND solver run in a child interpreter with a time
limit. A crash, a timeout or any other failure of that run costs the text and nothing else: the PROVED verdict
and the core stay, and the verdict says why there is no text (``detail`` and ``proof["text_unavailable"]``).

Every decision runs in a CHILD process, so that a regression is a failed assertion about an exit code and
not the death of the test run. The failures of the proof run itself (a crash, a hang, silence, a run that does
not reach ``unsat``) are simulated by replacing the program the proof child runs.
"""
import json
import subprocess
import sys

import pytest

pytest.importorskip("cvc5")

from unicode_logic_kit.atp import cvc5_backend
from unicode_logic_kit.eval.explain import explain_proof

# ∀x f(carl) = x ⊢ ∃w ∀x f(carl) = x: valid (the premise is the very sentence, the quantifier over w is vacuous)
CRASHING = {"premises": ["∀x f(carl) = x"], "goal": "∃w ∀x f(carl) = x"}
# ∀x (P(x) → Q(x)), P(a) ⊢ Q(a): valid (one instantiation, modus ponens)
ORDINARY = {"premises": ["∀x (P(x) → Q(x))", "P(a)"], "goal": "Q(a)"}

_CHILD = r"""
import json, subprocess, sys
from unicode_logic_kit import api
from unicode_logic_kit.atp import cvc5_backend
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend

spec = json.loads(sys.argv[1])
parse = lambda text: api.parse_any(text).formula
if spec.get("forbid_subprocess"):
    def refuse(*args, **kwargs):
        raise AssertionError("a child process was started on the default path")
    subprocess.run = refuse
mode = spec.get("simulate")
if mode:
    programs = {
        "crash": "import os\nos._exit(139)\n",
        "hang": "import time\ntime.sleep(120)\n",
        "silent": "pass\n",
        "garbage": "print('not json')\n",
        "no-unsat": "import json\nprint(json.dumps({'ok': False, 'why': 'the proof run answered unknown instead of unsat'}))\n",
    }
    cvc5_backend._PROOF_CHILD_SOURCE = programs[mode]
    cvc5_backend._PROOF_PROCESS_SLACK = 0.5
if spec.get("through_api"):
    verdict = api.prove(parse(spec["goal"]), [parse(p) for p in spec["premises"]],
                        backends=["cvc5"], timeout=spec.get("timeout", 20000), **spec["options"])
else:
    verdict = Cvc5Backend().decide(parse(spec["goal"]), [parse(p) for p in spec["premises"]],
                                   timeout=spec.get("timeout", 20000), **spec["options"])
print(json.dumps({"status": verdict.status, "backend": verdict.backend, "proof": verdict.proof,
                  "detail": verdict.detail, "wall_time": verdict.wall_time}))
"""


def decide(problem, *, options=None, **extra):
    """``Cvc5Backend().decide`` (or ``api.prove``) in a child process; the verdict as a dict."""
    spec = json.dumps({**problem, "options": options or {}, **extra})
    done = subprocess.run([sys.executable, "-c", _CHILD, spec], capture_output=True, text=True,
                          encoding="utf-8", timeout=600)
    # 0, not 3221225477 (Windows access violation) or -11 (SIGSEGV)
    assert done.returncode == 0, (done.returncode, done.stderr[-600:])
    return json.loads(done.stdout.strip().splitlines()[-1])


# ---------------------------------------------------------------------------------------------
# the default path
# ---------------------------------------------------------------------------------------------
def test_the_problem_that_ended_the_process_is_proved_on_the_default_path():
    verdict = decide(CRASHING, forbid_subprocess=True)
    assert verdict["status"] == "proved"
    proof = verdict["proof"]
    assert proof["kind"] == "cvc5_alethe"
    assert proof["text"] is None and proof["text_unavailable"].startswith("not requested")
    # the core is cvc5's own: the premise and the negated goal, and both are needed (each alone is satisfiable)
    core = proof["unsat_core"]
    assert len(core) == 2
    assert sum(entry.startswith("(forall") for entry in core) == 1 and sum(entry.startswith("(not") for entry in core) == 1
    assert verdict["detail"] is None


def test_an_ordinary_problem_on_the_default_path_has_a_core_and_no_text():
    verdict = decide(ORDINARY, forbid_subprocess=True)
    assert verdict["status"] == "proved"
    assert verdict["proof"]["text"] is None
    # P(a) and the universal are what the proof uses; the negated goal is the third entry
    assert len(verdict["proof"]["unsat_core"]) == 3
    assert any("(P a)" in entry for entry in verdict["proof"]["unsat_core"])


def test_through_api_prove_the_default_path_survives_that_problem_too():
    verdict = decide(CRASHING, through_api=True, forbid_subprocess=True)
    assert verdict["status"] == "proved" and verdict["backend"] == "cvc5"


# ---------------------------------------------------------------------------------------------
# on request
# ---------------------------------------------------------------------------------------------
def test_the_text_asked_for_is_the_alethe_proof():
    verdict = decide(ORDINARY, options={"proof": True})
    proof = verdict["proof"]
    assert verdict["status"] == "proved" and verdict["detail"] is None
    # an Alethe proof is a sequence of (assume ...) and (step ... :rule ...) forms, in the problem's own names
    assert ":rule" in proof["text"] and "(assume" in proof["text"] and "text_unavailable" not in proof
    assert "(P a)" in proof["text"] and len(proof["unsat_core"]) == 3


def test_the_text_asked_for_through_api_prove():
    verdict = decide(ORDINARY, through_api=True, options={"proof": True})
    assert verdict["status"] == "proved" and ":rule" in verdict["proof"]["text"]


def test_the_text_asked_for_on_the_problem_that_ended_the_process_leaves_verdict_and_core_alone():
    default = decide(CRASHING)
    asked = decide(CRASHING, options={"proof": True})
    assert asked["status"] == "proved" and asked["proof"]["unsat_core"] == default["proof"]["unsat_core"]
    if asked["proof"]["text"] is None:
        # the proof printer ended its process (cvc5 1.3.4 on this problem): the verdict says so
        reason = asked["proof"]["text_unavailable"]
        assert "abnormally" in reason and "verdict and the unsat core are from the main solve" in reason
        assert asked["detail"] == "no Alethe proof text: " + reason
    else:                                          # a cvc5 that prints this proof: then it is a proof
        assert ":rule" in asked["proof"]["text"]


@pytest.mark.parametrize("mode, phrase", [
    ("crash", "ended abnormally (exit code 139"),
    ("hang", "did not finish within 1.5 s"),
    ("silent", "printed no answer"),
    ("garbage", "printed no answer"),
    ("no-unsat", "answered unknown instead of unsat"),
])
def test_a_failing_proof_run_costs_the_text_and_nothing_else(mode, phrase):
    verdict = decide(ORDINARY, options={"proof": True}, simulate=mode, timeout=1000)
    assert verdict["status"] == "proved"
    assert len(verdict["proof"]["unsat_core"]) == 3                   # the core is the main solve's
    assert verdict["proof"]["text"] is None
    assert phrase in verdict["proof"]["text_unavailable"]
    assert verdict["detail"] == "no Alethe proof text: " + verdict["proof"]["text_unavailable"]


def test_no_interpreter_to_run_the_proof_in_is_a_reason_not_an_exception(monkeypatch):
    monkeypatch.setattr(sys, "executable", "")
    text, why = cvc5_backend._alethe_text("(check-sat)", "UF", 42, 1000)
    assert text is None and "no Python interpreter" in why


def test_an_interpreter_that_cannot_be_started_is_a_reason_not_an_exception(monkeypatch):
    monkeypatch.setattr(sys, "executable", "this-interpreter-does-not-exist")
    text, why = cvc5_backend._alethe_text("(check-sat)", "UF", 42, 1000)
    assert text is None and why.startswith("the proof run could not be started")


# ---------------------------------------------------------------------------------------------
# what reads the proof
# ---------------------------------------------------------------------------------------------
def test_explain_proof_says_that_no_text_was_recorded_and_still_gives_the_core():
    proof = {"kind": "cvc5_alethe", "text": None, "unsat_core": ["(P a)"],
             "text_unavailable": cvc5_backend._PROOF_NOT_REQUESTED}
    sentence = explain_proof(proof)
    assert "no Alethe proof text was recorded" in sentence and "(P a)" in sentence


def test_the_verdict_proof_is_json():
    verdict = decide(CRASHING, options={"proof": True})
    assert json.loads(json.dumps(verdict["proof"])) == verdict["proof"]
