r"""The labelled modal tableau's countermodel is a function of its input, whatever ``PYTHONHASHSEED`` is.

The search takes "the first" unexpanded branching formula, diamond or box obligation it meets, and the
diamond it takes first decides which world is numbered 1, which 2, and so on: the model read off an open
branch carries that numbering. A branch kept each world's formulas and its box obligations in ``set`` s, and a
``set`` of formulas (which hash their names) or of tuples that hold a relation name iterates in an order that
follows the hash seed of the process. The verdicts never changed (every order is a choice among complete
rules); the countermodel did, from one run of the same program to the next.

What is checked is a property of the process, so it is checked in child processes under five hash seeds.

The hand-derived cases, in the order the tableau meets the formulas (a formula is met in the order it was added
to the branch, and a conjunction adds its left conjunct first):

* ``¬(◇P1 ∧ (◇P2 ∧ … ∧ ◇P6))`` is falsified by a model where the root sees six worlds, world ``i`` holding
  ``Pi`` and nothing else: the diamonds are expanded left to right, and the ``i``-th creates world ``i``.
* ``¬((P ∨ Q) ∧ (¬P ∨ R))`` is falsified by making ``(P ∨ Q) ∧ (¬P ∨ R)`` true at the root. ``P ∨ Q`` is split
  first, its left disjunct ``P`` first; ``¬P ∨ R`` then closes on ``¬P`` and goes on with ``R``: the model makes
  ``P`` and ``R`` true at the root. Split the other disjunction first and the open branch would be ``{Q}``.
* ``¬(□P ∧ □Q)`` under the serial frame KD: the root holds ``□P`` and ``□Q`` and needs one successor, which
  holds ``P`` and ``Q``: worlds 0 and 1, one edge.

Besides them, 200 generated formulas over ``K, T, S4, S5, KD, KB, K4`` with box, diamond and the
connectives (and an epistemic operator) give the same verdicts and the same models under every seed.
"""

import json
import os
import subprocess
import sys

import pytest

import unicode_logic_kit

HASH_SEEDS = (0, 1, 2, 3, 4)

_CHILD = r'''
import json
import random
import sys

from unicode_logic_kit.atp.modal_tableau import modal_countermodel, modal_decide, modal_tableau_closed
from unicode_logic_kit.fol.nodes import And, Atom, Box, Constant, Diamond, Iff, Implies, Knows, Not, Or


def canonical(model):
    if model is None:
        return None
    return {
        "worlds": sorted(model.worlds),
        "relations": {name: sorted(map(list, edges)) for name, edges in sorted(model.relations.items())},
        "valuation": {str(w): sorted(atoms) for w, atoms in sorted(model.valuation.items())},
    }


def atom(name):
    return Atom(name, ())


def conjunction(parts):
    node = parts[-1]
    for part in reversed(parts[:-1]):
        node = And(part, node)
    return node


def generated(rng, depth):
    if depth == 0 or rng.random() < 0.18:
        return atom(rng.choice("PQRST"))
    kind = rng.choice(["and", "or", "imp", "not", "box", "box", "dia", "dia", "iff", "know"])
    if kind == "not":
        return Not(generated(rng, depth - 1))
    if kind == "box":
        return Box(generated(rng, depth - 1))
    if kind == "dia":
        return Diamond(generated(rng, depth - 1))
    if kind == "know":
        return Knows(Constant(rng.choice("ab")), generated(rng, depth - 1))
    left, right = generated(rng, depth - 1), generated(rng, depth - 1)
    return {"and": And, "or": Or, "imp": Implies, "iff": Iff}[kind](left, right)


out = {"cases": {}, "battery": []}
diamonds = Not(conjunction([Diamond(atom(f"P{i}")) for i in range(1, 7)]))
out["cases"]["six diamonds"] = canonical(modal_countermodel(diamonds, "K"))
split = Not(And(Or(atom("P"), atom("Q")), Or(Not(atom("P")), atom("R"))))
out["cases"]["two splits"] = canonical(modal_countermodel(split, "K"))
serial = Not(And(Box(atom("P")), Box(atom("Q"))))
out["cases"]["serial boxes"] = canonical(modal_countermodel(serial, "KD"))

frames = ["K", "T", "S4", "S5", "KD", "KB", "K4"]
for seed in range(int(sys.argv[1])):
    rng = random.Random(seed)
    formula = generated(rng, rng.randint(2, 5))
    frame = rng.choice(frames)
    out["battery"].append([
        seed, frame,
        modal_tableau_closed([Not(formula)], frame=frame, max_steps=20000),
        modal_decide(formula, frame=frame, max_steps=20000),
        canonical(modal_countermodel(formula, frame=frame, max_steps=20000)),
    ])
print(json.dumps(out, sort_keys=True))
'''

FORMULAS = 200


def _run_child(hash_seed):
    root = os.path.dirname(os.path.dirname(os.path.abspath(unicode_logic_kit.__file__)))
    env = dict(os.environ, PYTHONHASHSEED=str(hash_seed), PYTHONIOENCODING="utf-8",
               PYTHONPATH=os.pathsep.join([root] + [p for p in os.environ.get("PYTHONPATH", "").split(os.pathsep) if p]))
    done = subprocess.run([sys.executable, "-c", _CHILD, str(FORMULAS)], env=env, capture_output=True,
                          text=True, encoding="utf-8", timeout=300)
    assert done.returncode == 0, done.stderr[-2000:]
    return json.loads(done.stdout)


@pytest.fixture(scope="module")
def runs():
    return {seed: _run_child(seed) for seed in HASH_SEEDS}


def test_the_hand_derived_countermodels_are_the_same_under_every_hash_seed(runs):
    six = {"worlds": list(range(7)),
           "relations": {"alethic": [[0, i] for i in range(1, 7)]},
           "valuation": {"0": [], **{str(i): [f"P{i}"] for i in range(1, 7)}}}
    splits = {"worlds": [0], "relations": {}, "valuation": {"0": ["P", "R"]}}
    # KD is serial: world 1, the one successor, needs a successor of its own and sees itself. The
    # relation {(0, 1)} is not a KD frame (world 1 has no successor), so a model with only that
    # edge is no countermodel under KD.
    serial = {"worlds": [0, 1], "relations": {"alethic": [[0, 1], [1, 1]]},
              "valuation": {"0": [], "1": ["P", "Q"]}}
    for seed, run in runs.items():
        assert run["cases"]["six diamonds"] == six, f"hash seed {seed}"
        assert run["cases"]["two splits"] == splits, f"hash seed {seed}"
        assert run["cases"]["serial boxes"] == serial, f"hash seed {seed}"


def test_generated_formulas_get_one_verdict_and_one_model_under_every_hash_seed(runs):
    reference = runs[HASH_SEEDS[0]]["battery"]
    assert len(reference) == FORMULAS
    assert sum(1 for row in reference if row[4] is not None) >= 150      # most of them have a countermodel
    for seed in HASH_SEEDS[1:]:
        different = [row[0] for row, ref in zip(runs[seed]["battery"], reference) if row != ref]
        assert not different, f"hash seed {seed} differs from seed {HASH_SEEDS[0]} for formulas {different[:10]}"


def test_the_verdicts_of_the_generated_formulas_agree_with_their_models(runs):
    # "valid" is the closed tableau, "invalid" an open branch whose model satisfies_modal verified, and a
    # formula with neither is "unknown" and has no model.
    battery = runs[HASH_SEEDS[0]]["battery"]
    for _seed, _frame, closed, decision, model in battery:
        assert decision in ("valid", "invalid", "unknown")
        assert (decision == "valid") == closed
        assert (decision == "invalid") == (model is not None)
    assert sum(1 for row in battery if row[3] != "unknown") >= 0.9 * len(battery)


# ---------------------------------------------------------------------------
# The container
# ---------------------------------------------------------------------------

def test_an_ordered_set_iterates_in_insertion_order_and_keeps_the_place_of_a_member_added_twice():
    from unicode_logic_kit.atp.modal_tableau import _OrderedSet

    members = _OrderedSet()
    for name in ["delta", "alpha", "charlie", "bravo", "alpha"]:
        members.add(name)
    assert list(members) == ["delta", "alpha", "charlie", "bravo"]
    assert "charlie" in members and "echo" not in members and len(members) == 4


def test_a_copy_of_an_ordered_set_is_independent_and_keeps_the_order():
    from unicode_logic_kit.atp.modal_tableau import _OrderedSet

    original = _OrderedSet()
    for name in ["z", "y", "x"]:
        original.add(name)
    duplicate = original.copy()
    duplicate.add("w")
    assert list(original) == ["z", "y", "x"] and list(duplicate) == ["z", "y", "x", "w"]


def test_an_ordered_set_compares_as_a_subset_like_a_set():
    from unicode_logic_kit.atp.modal_tableau import _OrderedSet

    small, large = _OrderedSet(), _OrderedSet()
    for name in ["a", "b"]:
        small.add(name)
    for name in ["c", "b", "a"]:
        large.add(name)
    assert small <= large and not (large <= small) and small <= small
