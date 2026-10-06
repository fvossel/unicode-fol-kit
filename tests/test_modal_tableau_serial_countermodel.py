r"""A countermodel of the labelled modal tableau is a model of the frame class that was asked for.

The search gives a world a successor when the world has a box obligation and none, so that a serial
relation is serial where it matters. Its last world, the one a diamond created or the one that was made
to witness a box, is a dead end if it has no box obligation of its own, and a dead end is no world of a
serial frame: ``□Q(dora)`` over the frame ``D`` has the countermodel ``{0, 1}`` with the one edge ``0 → 1``
and ``Q(dora)`` false at 1 as far as ``satisfies_modal`` can tell (it evaluates the relations as they are
and knows no frame), but the relation is not serial. The model that is read off now lets every dead end of a
serial relation see itself, and it is handed out only when ``satisfies_modal`` says the formula is false at
the root AND every relation satisfies the conditions of its system.

By hand, over the serial frames ``D = KD`` and ``KD4`` (serial and transitive):

* ``□Q(dora)`` is false at the root of a model with two worlds: the root sees world 1, where ``Q(dora)`` is
  false, and world 1 sees itself. ``R = {(0, 1), (1, 1)}``. It is serial, and transitive: the only
  two-step paths are ``0 → 1 → 1`` and ``1 → 1 → 1``, and ``(0, 1)`` and ``(1, 1)`` are in ``R``.
* ``Ⓞ Q(dora)`` under the default deontic system, ``KD``: the same model for the deontic relation.
* ``¬(□P ∧ ⓄQ)`` with the alethic frame ``D``: the root holds ``□P`` and ``ⓄQ`` and so needs an alethic
  successor with ``P`` and a deontic successor with ``Q``; both are dead ends and both see themselves in
  each of the two relations.
"""

import itertools
import random

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import modal_tableau as MT
from unicode_fol_kit.atp.modal_tableau import modal_countermodel, modal_decide
from unicode_fol_kit.fol.frames import FRAMES, holds_on_finite_frame, resolve_frame
from unicode_fol_kit.fol.nodes import (And, Atom, Believes, Box, Constant, Diamond, DistributedKnowledge,
                                       EverybodyKnows, Iff, Implies, Knows, Next, Not, Obligatory, Or,
                                       Permitted)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

Q_DORA = Atom("Q", [Constant("dora")])


def _holds(model, relation, conditions):
    edges = frozenset(model.relations.get(relation, ()))
    return all(holds_on_finite_frame(c, edges, len(model.worlds)) for c in conditions)


# ---------------------------------------------------------------------------------------------
# the hand-derived models
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("frame", ["D", "KD", "KD4"])
def test_a_box_over_a_serial_frame_has_the_countermodel_with_a_self_loop(frame):
    formula = Box(Q_DORA)
    model = modal_countermodel(formula, frame=frame)
    assert model is not None
    assert set(model.worlds) == {0, 1}
    assert set(model.relations["alethic"]) == {(0, 1), (1, 1)}
    assert not satisfies_modal(formula, model, 0)
    assert _holds(model, "alethic", resolve_frame(frame))
    assert modal_decide(formula, frame=frame) == "invalid"


def test_the_deontic_relation_of_an_obligation_is_serial_by_default():
    formula = Obligatory(Q_DORA)
    model = modal_countermodel(formula)                     # frame K for the alethic relation, KD for the deontic
    assert model is not None
    assert set(model.worlds) == {0, 1}
    assert set(model.relations["deontic"]) == {(0, 1), (1, 1)}
    assert "alethic" not in model.relations                 # a relation the formula does not mention is not made up
    assert not satisfies_modal(formula, model, 0)
    assert _holds(model, "deontic", FRAMES["KD"])


def test_two_serial_relations_are_each_completed():
    p, q = Atom("P", []), Atom("Q", [])
    formula = Not(And(Box(p), Obligatory(q)))
    model = modal_countermodel(formula, frame="D")
    assert model is not None
    assert not satisfies_modal(formula, model, 0)
    assert _holds(model, "alethic", FRAMES["D"]) and _holds(model, "deontic", FRAMES["KD"])
    alethic_successors = {v for (w, v) in model.relations["alethic"] if w == 0}
    deontic_successors = {v for (w, v) in model.relations["deontic"] if w == 0}
    assert alethic_successors and all("P" in model.valuation[v] for v in alethic_successors)
    assert deontic_successors and all("Q" in model.valuation[v] for v in deontic_successors)


def test_a_relation_that_is_not_serial_stays_as_it_is():
    # over K a dead end is a dead end: □Q(dora) is falsified by {0 → 1} alone, as it always was
    model = modal_countermodel(Box(Q_DORA), frame="K")
    assert set(model.relations["alethic"]) == {(0, 1)}


def test_the_default_deontic_system_gives_the_api_countermodel_too():
    verdict = api.prove(Obligatory(Q_DORA), [], backends=["modal-tableau"], logic="modal", timeout=5000)
    assert verdict.status == "refuted"
    assert sorted(map(list, verdict.countermodel["data"]["relations"]["deontic"])) == [[0, 1], [1, 1]]
    verdict = api.prove(Box(Q_DORA), [], backends=["modal-tableau"], logic="modal", frame="D", timeout=5000)
    assert sorted(map(list, verdict.countermodel["data"]["relations"]["alethic"])) == [[0, 1], [1, 1]]


def test_a_model_that_is_not_of_the_frame_is_never_handed_out(monkeypatch):
    # Suppose the search left a dead end that nothing completed: the model it would read off is the
    # one with the single edge. satisfies_modal accepts it; the frame check does not.
    def read_off_without_completion(branch, ctx=None):
        always = {fact.to_unicode_str() for fact in branch.facts}
        valuation = {w: {f.to_unicode_str() for f in formulas if isinstance(f, Atom)} | always
                     for w, formulas in branch.tv.items()}
        relations = {name: set(edges) for name, edges in branch.rels.items()}
        return KripkeModel(set(branch.tv) | {0}, relations, valuation)

    monkeypatch.setattr(MT, "_build_model", read_off_without_completion)
    formula = Box(Q_DORA)
    assert modal_countermodel(formula, frame="D") is None
    assert modal_decide(formula, frame="D") == "unknown"
    # a frame that asks nothing of the dead end is not affected
    assert modal_countermodel(formula, frame="K") is not None
    assert modal_decide(formula, frame="K") == "invalid"


# ---------------------------------------------------------------------------------------------
# the check the search makes, against the registry of the kit
# ---------------------------------------------------------------------------------------------
def test_the_frame_check_of_the_tableau_agrees_with_the_registry_on_every_frame_up_to_three_worlds():
    conditions = ["refl", "trans", "sym", "serial", "eucl"]
    for size in (1, 2, 3):
        cells = list(itertools.product(range(size), repeat=2))
        for mask in range(1 << len(cells)):
            edges = frozenset(cell for k, cell in enumerate(cells) if mask >> k & 1)
            for condition in conditions:
                assert (MT._frame_condition_holds(condition, edges, set(range(size)))
                        == holds_on_finite_frame(condition, edges, size)), (size, sorted(edges), condition)


def test_the_frame_check_of_the_tableau_reads_a_model_with_many_worlds():
    # the registry's own check grows with about the fourth power of the number of worlds, which a model
    # of a few hundred worlds cannot afford; this one is linear in the edges and their out-degrees
    n = 120
    chain = {(i, j) for i in range(n) for j in range(i, n)}           # a reflexive, transitive order
    assert MT._frame_condition_holds("trans", chain, set(range(n)))
    assert MT._frame_condition_holds("serial", chain, set(range(n)))
    assert not MT._frame_condition_holds("sym", chain, set(range(n)))
    assert not MT._frame_condition_holds("eucl", chain, set(range(n)))


# ---------------------------------------------------------------------------------------------
# generated formulas: every model handed out is a model of the frame (the registry is the judge)
# ---------------------------------------------------------------------------------------------
_AGENTS = (Constant("a"), Constant("b"))


def _random_formula(rng, depth, flavour):
    if depth <= 0 or rng.random() < 0.15:
        return Atom(rng.choice("pqr"), [])
    kinds = ["not", "and", "or", "imp", "iff"]
    modal = {
        "alethic": ["box", "dia", "box", "dia"],
        "deontic": ["obl", "per", "box", "dia"],
        "epistemic": ["know", "bel", "box", "dia"],
        "group": ["know", "ek", "dk", "box"],
        "temporal": ["next", "box", "dia"],
    }[flavour]
    kind = rng.choice(kinds + modal + modal)

    def sub():
        return _random_formula(rng, depth - 1, flavour)

    if kind == "not":
        return Not(sub())
    if kind == "box":
        return Box(sub())
    if kind == "dia":
        return Diamond(sub())
    if kind == "obl":
        return Obligatory(sub())
    if kind == "per":
        return Permitted(sub())
    if kind == "know":
        return Knows(rng.choice(_AGENTS), sub())
    if kind == "bel":
        return Believes(rng.choice(_AGENTS), sub())
    if kind == "ek":
        return EverybodyKnows(_AGENTS, sub())
    if kind == "dk":
        return DistributedKnowledge(_AGENTS, sub())
    if kind == "next":
        return Next(sub())
    return {"and": And, "or": Or, "imp": Implies, "iff": Iff}[kind](sub(), sub())


#: (flavour of formula, alethic frame, systems of the other relations)
CONFIGURATIONS = [
    ("alethic", "D", None), ("alethic", "KD4", None), ("alethic", "KD5", None), ("alethic", "KD45", None),
    ("alethic", "S4", None), ("deontic", "K", None), ("deontic", "K", {"deontic": "KD45"}),
    ("deontic", "T", {"deontic": "KD4"}), ("epistemic", "K", {"epistemic": "KD", "doxastic": "KD45"}),
    ("epistemic", "K", {"epistemic": "S5"}), ("group", "K", {"epistemic": "KD"}),
    ("temporal", "K", {"temporal": "KD4"}),
]


def _conditions(relation, frame, systems):
    systems = systems or {}
    if relation == "alethic":
        return FRAMES[frame]
    if relation == "deontic":
        return FRAMES[systems.get("deontic", "KD")]
    if relation == "temporal":
        return FRAMES[systems.get("temporal", "K")]
    if relation.startswith("K:"):
        return FRAMES[systems.get("epistemic", "K")]
    if relation.startswith("B:"):
        return FRAMES[systems.get("doxastic", "K")]
    return ()


def test_every_countermodel_of_generated_formulas_is_a_model_of_its_frame_and_falsifies_the_formula():
    rng = random.Random(20260905)
    handed_out = completed_dead_ends = 0
    for _ in range(40):
        for flavour, frame, systems in CONFIGURATIONS:
            formula = _random_formula(rng, rng.randint(2, 4), flavour)
            options = dict(frame=frame, systems=systems, max_worlds=10, max_steps=20000, timeout=4000)
            model = modal_countermodel(formula, **options)
            if model is None:
                continue
            handed_out += 1
            assert not satisfies_modal(formula, model, 0), formula.to_unicode_str()
            n = len(model.worlds)
            assert set(model.worlds) == set(range(n))
            for relation, edges in model.relations.items():
                conditions = _conditions(relation, frame, systems)
                for condition in conditions:
                    assert holds_on_finite_frame(condition, frozenset(edges), n), (
                        f"{formula.to_unicode_str()} over {frame} {systems}: the relation {relation!r} "
                        f"{sorted(edges)} on {n} worlds is not {condition}")
                if "serial" in conditions:
                    # a world whose only successor is itself, in a relation that is not reflexive
                    completed_dead_ends += sum(
                        1 for w in range(n) if {v for (a, v) in edges if a == w} == {w}
                        and "refl" not in conditions)
    assert handed_out >= 300, handed_out
    assert completed_dead_ends >= 150, completed_dead_ends   # the completion was exercised, not only possible


def test_the_default_chain_of_a_serial_frame_gives_a_model_of_that_frame():
    # ¬◇□r is false in a KD4 model where the root sees a world whose successors all hold r:
    # r holds at world 1, and world 1 sees itself
    formula = Not(Diamond(Box(Atom("r", []))))
    verdict = api.prove(formula, [], backends=["modal-tableau"], logic="modal", frame="KD4", timeout=5000)
    assert verdict.status == "refuted"
    data = verdict.countermodel["data"]
    n = len(data["worlds"])
    edges = frozenset(tuple(e) for e in data["relations"]["alethic"])
    assert all(holds_on_finite_frame(c, edges, n) for c in resolve_frame("KD4"))
