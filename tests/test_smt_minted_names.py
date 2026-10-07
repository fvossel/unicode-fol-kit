"""Z3 and cvc5 against a brute-force enumeration, on problems whose symbols are named like the kit's minted names.

The kit mints names: the tracking literals of the Z3 backend (``goal``, ``p0``, ``p1``), the witnesses of a
counting quantifier and of a sort's non-emptiness axiom (``x0``, ``x1``, ``y0``), Skolem symbols (``_sk0``),
the marks of the Z3 environment (``x!v``, ``a!c``) and the tokens of the SMT-LIB sanitiser. A name that a
problem uses for ITS symbol -- a proposition ``goal``, a predicate, function, constant or sort ``x0`` -- must
never be mistaken for one of them, and a text with ONE namespace for every kind of symbol (SMT-LIB) must not
read a bound witness as the predicate of the same name (cvc5 ends the process on that).

``_minted_name_problems`` generates small problems, with plain, sorted and counting quantifiers, in which every
kind of symbol is drawn from that stock of names, and enumerates every structure of at most two elements
(``∀x ∀y ∀z (x = y ∨ x = z ∨ y = z)`` is a premise of each, so "no countermodel of at most two elements" is
validity). Hand-checked on the fly, the enumeration shares no code with the kit.

* ``Z3Backend``, an ``IncrementalSession`` and the SMT-LIB text written by ``to_smtlib`` (read by Z3's own
  parser) give the verdict of the enumeration on every problem; the premises ``z3_relevant_premises`` reports
  still entail the goal.
* cvc5 never gives the opposite verdict, and never ends the process: it runs in a CHILD process, so that a
  failure is an assertion about an exit code and not the death of the test run.
"""
import json
import subprocess
import sys

import pytest
import z3

from _minted_name_problems import AT_MOST_TWO, has_countermodel, make_problem
from unicode_logic_kit.atp.incremental import IncrementalSession
from unicode_logic_kit.atp.protocol import PROVED, REFUTED, Z3Backend, z3_relevant_premises
from unicode_logic_kit.atp.z3_input import to_smtlib
from unicode_logic_kit.fol._msfl_nodes import sort_axioms
from unicode_logic_kit.fol.nodes import Not

SEEDS = range(1, 241)
CVC5_SEEDS = range(1, 121)


class Problem:
    def __init__(self, seed):
        self.seed = seed
        premises, self.goal, self.symbols = make_problem(seed)
        self.premises = premises + [AT_MOST_TWO]
        self.has_countermodel = has_countermodel(self.premises, self.goal, self.symbols)


@pytest.fixture(scope="module")
def problems():
    return [Problem(seed) for seed in SEEDS]


def test_the_batch_has_valid_and_invalid_problems(problems):
    valid = sum(not p.has_countermodel for p in problems)
    assert valid >= 40 and len(problems) - valid >= 40, (valid, len(problems))


def test_the_batch_uses_the_minted_names_for_several_kinds_of_symbol(problems):
    # a name that is a proposition in one problem and a sort, a function, a constant or a predicate in
    # another: the stock is small, so the problems reuse a name across kinds all the time
    reused = [p.seed for p in problems
              if set(p.symbols.propositions) & (set(p.symbols.constants) | set(p.symbols.functions)
                                                | set(p.symbols.predicates) | {p.symbols.sort})]
    assert len(reused) >= 10, reused
    for name in ("goal", "p0", "x0", "y0"):
        assert any(name in p.symbols.propositions for p in problems), name


def test_z3_gives_the_verdict_of_the_enumeration(problems):
    wrong = []
    for p in problems:
        verdict = Z3Backend().decide(p.goal, p.premises)
        assert verdict.status in (PROVED, REFUTED), (p.seed, verdict.status, verdict.detail)
        if (verdict.status == REFUTED) != p.has_countermodel:
            wrong.append((p.seed, verdict.status, p.has_countermodel))
    assert wrong == []


def test_an_incremental_session_gives_the_verdict_of_the_enumeration(problems):
    wrong = []
    for p in problems:
        verdict = IncrementalSession(p.premises).decide(p.goal)
        assert verdict.status in (PROVED, REFUTED), (p.seed, verdict.status, verdict.detail)
        if (verdict.status == REFUTED) != p.has_countermodel:
            wrong.append((p.seed, verdict.status, p.has_countermodel))
    assert wrong == []


def test_the_premises_z3_calls_relevant_still_entail_the_goal(problems):
    for p in problems:
        if p.has_countermodel:
            assert z3_relevant_premises(p.goal, p.premises) is None, p.seed
            continue
        relevant = z3_relevant_premises(p.goal, p.premises)
        assert relevant is not None, p.seed
        assert not has_countermodel([p.premises[i] for i in relevant], p.goal, p.symbols), (p.seed, relevant)


def test_the_smtlib_text_is_satisfiable_with_the_negated_goal_exactly_when_there_is_a_countermodel(problems):
    # to_smtlib writes no sort axioms (they are background of the solver routes); handing them over as
    # premises makes the text the whole problem. Z3's own parser reads the text, so a witness named like a
    # predicate (``(exists ((x0 S)) (x0 x0))``) is a parse error here.
    wrong = []
    for p in problems:
        axioms = list(sort_axioms(p.goal, *p.premises))
        text = to_smtlib(Not(p.goal), p.premises + axioms)
        solver = z3.Solver()
        solver.set("timeout", 20000)
        solver.add(z3.parse_smt2_string(text))
        result = solver.check()
        assert result in (z3.sat, z3.unsat), (p.seed, result)
        # premises ∧ ¬goal is satisfiable exactly when the goal does not follow
        if (result == z3.sat) != p.has_countermodel:
            wrong.append((p.seed, str(result), p.has_countermodel))
    assert wrong == []


# ---------------------------------------------------------------------------------------------------------
# cvc5, in a child process
# ---------------------------------------------------------------------------------------------------------
_CHILD = r"""
import json, sys
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
from unicode_logic_kit.fol.nodes import Node

for line in sys.stdin.read().splitlines():
    spec = json.loads(line)
    premises = [Node.from_dict(d) for d in spec["premises"]]
    goal = Node.from_dict(spec["goal"])
    print(json.dumps({"seed": spec["seed"], "status": "started"}), flush=True)
    verdict = Cvc5Backend().decide(goal, premises, timeout=20000)
    print(json.dumps({"seed": spec["seed"], "status": verdict.status, "detail": verdict.detail}), flush=True)
"""


@pytest.fixture(scope="module")
def cvc5_verdicts(problems):
    pytest.importorskip("cvc5")
    chosen = [p for p in problems if p.seed in CVC5_SEEDS]
    lines = "\n".join(json.dumps({"seed": p.seed, "goal": p.goal.to_dict(),
                                 "premises": [q.to_dict() for q in p.premises]}) for p in chosen)
    done = subprocess.run([sys.executable, "-c", _CHILD], input=lines, capture_output=True, text=True,
                          encoding="utf-8", timeout=600)
    answers = [json.loads(line) for line in done.stdout.splitlines()]
    assert done.returncode == 0, (
        f"the cvc5 child process ended with exit code {done.returncode & 0xFFFFFFFF:#x} on seed "
        f"{answers[-1]['seed'] if answers else '?'}")
    return {a["seed"]: a for a in answers if a["status"] != "started"}


def test_cvc5_never_ends_the_process_and_never_gives_the_opposite_verdict(problems, cvc5_verdicts):
    assert set(cvc5_verdicts) == set(CVC5_SEEDS)
    wrong = []
    for p in problems:
        if p.seed not in CVC5_SEEDS:
            continue
        status = cvc5_verdicts[p.seed]["status"]
        assert status != "error", (p.seed, cvc5_verdicts[p.seed]["detail"])
        if (status == "proved" and p.has_countermodel) or (status == "refuted" and not p.has_countermodel):
            wrong.append((p.seed, status, p.has_countermodel))
    assert wrong == []


def test_cvc5_proves_most_of_the_valid_problems(problems, cvc5_verdicts):
    # cvc5 answers unknown on a problem with a countermodel under the at-most-two premise (quantified, no
    # finite model found); the valid ones it mostly proves, so the check above is not vacuous
    valid = [p.seed for p in problems if p.seed in CVC5_SEEDS and not p.has_countermodel]
    proved = [s for s in valid if cvc5_verdicts[s]["status"] == "proved"]
    assert len(proved) >= len(valid) * 0.8, (len(proved), len(valid))
