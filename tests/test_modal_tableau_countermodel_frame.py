r"""A countermodel of the modal tableau is a model of the frame, for EVERY relation its formula mentions.

The tableau reads a countermodel off an open branch. A relation the formula mentions in a disjunct the
branch never uses has no edge on the branch and so no entry in the model, and an absent relation is the
empty relation, which is neither reflexive nor serial: ``¬(A ∨ □Q)`` over the frame ``T`` has the open
branch ``{A}`` and its model had ``alethic = ∅`` — a model of the frame ``K``, not of ``T``.

The oracle of this file shares nothing with the kit's check: the frame conditions of each named system are
written out below as sets of the five properties of a binary relation (reflexive, symmetric, transitive,
euclidean, serial), each decided by a direct reading of its definition on the edge set; and the truth value
of the formula in the model is decided by an evaluator of this file, not by ``satisfies_modal``.

By hand, over ONE world ``{0}`` the only relations are ``∅`` and ``{(0, 0)}``. ``∅`` is not reflexive and
not serial; ``{(0, 0)}`` is reflexive, symmetric, transitive, euclidean and serial. So whatever a model with
one world and a reflexive / serial / equivalence relation has, its relation IS ``{(0, 0)}``.
"""

import itertools
import random
import zlib

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.modal_tableau import modal_countermodel, modal_decide
from unicode_fol_kit.fol.nodes import (
    And, Atom, Box, Constant, Diamond, DistributedKnowledge, Iff, Implies, Knows, Not, Obligatory,
    Or, Permitted,
)

A, B, Q = Atom("A", []), Atom("B", []), Atom("Q", [])
AG, BG = Constant("ag"), Constant("bg")

#: the conditions of each named system, from the textbook definitions of the systems
CONDITIONS = {
    "K": (), "T": ("refl",), "D": ("serial",), "KD": ("serial",), "K4": ("trans",),
    "K45": ("trans", "eucl"), "S4": ("refl", "trans"), "S5": ("refl", "sym", "trans"),
    "KD45": ("serial", "trans", "eucl"),
}


def has_property(prop, edges, worlds):
    """``prop`` of the relation ``edges`` over ``worlds``, by the definition."""
    edges = set(edges)
    if prop == "refl":
        return all((w, w) in edges for w in worlds)
    if prop == "sym":
        return all((b, a) in edges for (a, b) in edges)
    if prop == "trans":
        return all((a, c) in edges for (a, b) in edges for (b2, c) in edges if b == b2)
    if prop == "eucl":
        return all((b, c) in edges for (a, b) in edges for (a2, c) in edges if a == a2)
    if prop == "serial":
        return all(any((w, v) in edges for v in worlds) for w in worlds)
    raise AssertionError(prop)


def frame_problems(model, system_of):
    """Every (relation, property) a relation of ``model`` lacks, for the relations named in ``system_of``.

    ``system_of`` maps a relation name to the system whose conditions it has to meet. An absent relation
    is the empty relation.
    """
    problems = []
    for name, system in system_of.items():
        edges = set(model.relations.get(name, ()))
        for prop in CONDITIONS[system]:
            if not has_property(prop, edges, model.worlds):
                problems.append((name, prop, sorted(edges)))
    return problems


# ---------------------------------------------------------------------------------------------
# the evaluator of the oracle
# ---------------------------------------------------------------------------------------------
def _successors(model, relation, world):
    return [v for (w, v) in model.relations.get(relation, ()) if w == world]


def true_at(f, model, world):
    if isinstance(f, Atom):
        return f.to_unicode_str() in model.valuation.get(world, ())
    if isinstance(f, Not):
        return not true_at(f.formula, model, world)
    if isinstance(f, And):
        return true_at(f.left, model, world) and true_at(f.right, model, world)
    if isinstance(f, Or):
        return true_at(f.left, model, world) or true_at(f.right, model, world)
    if isinstance(f, Implies):
        return (not true_at(f.left, model, world)) or true_at(f.right, model, world)
    if isinstance(f, Iff):
        return true_at(f.left, model, world) == true_at(f.right, model, world)
    if isinstance(f, DistributedKnowledge):
        # what the group knows together: true in every world every member still considers possible
        shared = None
        for agent in f.group:
            seen = set(_successors(model, "K:" + agent.name, world))
            shared = seen if shared is None else shared & seen
        return all(true_at(f.formula, model, v) for v in shared)
    relation = {Box: "alethic", Diamond: "alethic", Obligatory: "deontic", Permitted: "deontic",
                Knows: "K:" + AG.name}[type(f)]
    inner = f.formula
    successors = _successors(model, relation, world)
    if isinstance(f, (Box, Obligatory, Knows)):
        return all(true_at(inner, model, v) for v in successors)
    return any(true_at(inner, model, v) for v in successors)


def relations_mentioned(f):
    """The relation names ``f`` reads, by scanning it."""
    names = set()
    for node in f.walk():
        if isinstance(node, (Box, Diamond)):
            names.add("alethic")
        elif isinstance(node, (Obligatory, Permitted)):
            names.add("deontic")
        elif isinstance(node, Knows):
            names.add("K:ag")
        elif isinstance(node, DistributedKnowledge):
            names.update("K:" + agent.name for agent in node.group)
    return names


def system_for(relation, frame, systems):
    if relation == "alethic":
        return frame
    if relation == "deontic":
        return (systems or {}).get("deontic", "KD")
    return (systems or {}).get("epistemic", "K")


def check_model(f, frame, systems=None):
    """Ask for a countermodel and check what is handed out; return it, or None when none is."""
    model = modal_countermodel(f, frame=frame, systems=systems)
    if model is None:
        return None
    assert not true_at(f, model, 0), "the model does not falsify the formula"
    wanted = {name: system_for(name, frame, systems) for name in relations_mentioned(f)}
    assert frame_problems(model, wanted) == [], (
        "not a model of the frame", sorted(model.worlds), {k: sorted(v) for k, v in model.relations.items()})
    return model


# ---------------------------------------------------------------------------------------------
# the cases of the defect: a modal operator in a disjunct the open branch does not use
# ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("frame", ["T", "S4", "S5", "D", "KD45"])
def test_a_dormant_box_gets_the_relation_of_the_frame(frame):
    # ¬(A ∨ □Q): the countermodel makes A ∨ □Q true at the root. The branch {A} does it with no use
    # of □Q, so the alethic relation has no edge on it. On ONE world the relation of each of these
    # frames is {(0, 0)}: reflexive (T, S4, S5), serial (D, KD45).
    formula = Not(Or(A, Box(Q)))
    model = check_model(formula, frame)
    assert model is not None
    if set(model.worlds) == {0}:
        assert set(model.relations["alethic"]) == {(0, 0)}


def test_a_dormant_obligation_gets_a_serial_deontic_relation():
    # ¬(A ∨ ⓄQ) under the default deontic system KD: the root needs a deontic successor.
    formula = Not(Or(A, Obligatory(Q)))
    model = check_model(formula, "K")
    assert model is not None
    if set(model.worlds) == {0}:
        assert set(model.relations["deontic"]) == {(0, 0)}


def test_a_dormant_knowledge_operator_gets_an_equivalence_relation_under_s5():
    formula = Not(Or(A, Knows(AG, Q)))
    model = check_model(formula, "K", {"epistemic": "S5"})
    assert model is not None
    if set(model.worlds) == {0}:
        assert set(model.relations["K:ag"]) == {(0, 0)}


def test_every_dormant_relation_is_completed_not_only_the_first():
    # three relations, each in a disjunct the branch {A} leaves unused; the frames: alethic T,
    # deontic KD (the default), epistemic S5.
    formula = Not(Or(A, Or(Box(Q), Or(Obligatory(B), Knows(AG, Q)))))
    model = check_model(formula, "T", {"epistemic": "S5"})
    assert model is not None
    assert {"alethic", "deontic", "K:ag"} <= set(model.relations)


def test_a_dormant_diamond_gets_the_relation_too():
    # ¬(A ∨ ◇Q): the branch {A} never creates the successor ◇Q would ask for.
    for frame in ("T", "S5", "D"):
        assert check_model(Not(Or(A, Diamond(Q))), frame) is not None


def test_a_group_knowledge_formula_has_a_countermodel_whose_group_relations_are_s5():
    # D_{ag,bg} Q is not valid: take ONE world with Q false; both agents' relations are S5, so
    # both are {(0, 0)}, their intersection is {(0, 0)} and D_G Q reads Q at world 0: false. With
    # an agent's relation empty (the relation the branch never used) the intersection is empty
    # and D_G Q is true vacuously, which is no countermodel.
    formula = DistributedKnowledge((AG, BG), Q)
    model = check_model(formula, "K", {"epistemic": "S5"})
    assert model is not None
    assert modal_decide(formula, frame="K", systems={"epistemic": "S5"}) == "invalid"
    for agent in ("K:ag", "K:bg"):
        assert all((w, w) in set(model.relations[agent]) for w in model.worlds)


def test_the_search_goes_on_when_a_branch_has_a_construct_it_has_no_rule_for():
    # D_{ag,bg} Q ∧ Ⓟ¬A over S4, the deontic system KD by default. The formula is false at the
    # root of ONE world where A holds and the deontic relation is {(0, 0)}: the only deontic
    # successor has A, so Ⓟ¬A is false. The negation is a branch ¬D_G Q (no rule for it: the tableau
    # leaves it on the branch) and a branch ⓄA. The first one is open, but the model read off it
    # (deontic loops, A false) makes Ⓟ¬A true and D_G Q true, so it is not a countermodel; the
    # second gives the one above. Whichever is first, the answer is the countermodel.
    formula = And(DistributedKnowledge((AG, BG), Q), Permitted(Not(A)))
    model = check_model(formula, "S4")
    assert model is not None
    assert modal_decide(formula, frame="S4") == "invalid"


def test_a_relation_the_formula_does_not_mention_is_not_made_up():
    # the formula reads no modal operator, so no relation is its business (nothing could tell the
    # difference): the model has none, as it always had.
    model = modal_countermodel(A, frame="T")
    assert model is not None
    assert "alethic" not in model.relations


def test_the_verdict_is_still_invalid():
    for frame in ("T", "S4", "S5", "D", "KD45"):
        assert modal_decide(Not(Or(A, Box(Q))), frame=frame) == "invalid"
    assert modal_decide(Not(Or(A, Obligatory(Q)))) == "invalid"


def test_the_api_countermodel_carries_the_relation_too():
    formula = Not(Or(A, Box(Q)))
    verdict = api.prove(formula, [], backends=["modal-tableau"], logic="modal", frame="T", timeout=5000)
    assert verdict.status == "refuted"
    edges = {tuple(e) for e in verdict.countermodel["data"]["relations"]["alethic"]}
    assert (0, 0) in edges
    found = api.countermodel(formula, [], logic="modal", backends=["modal-tableau"], frame="T")
    assert found.found
    assert {tuple(e) for e in found.model["data"]["relations"]["alethic"]} >= {(0, 0)}


# ---------------------------------------------------------------------------------------------
# the brute-force check on random formulas
# ---------------------------------------------------------------------------------------------
def random_formula(rng, depth, kinds):
    r = rng.random()
    if depth == 0 or r < 0.2:
        return rng.choice((A, B, Q))
    if r < 0.45:
        if rng.random() < 0.3:
            return Not(random_formula(rng, depth - 1, kinds))
        connective = rng.choice((And, Or, Implies, Iff))
        return connective(random_formula(rng, depth - 1, kinds), random_formula(rng, depth - 1, kinds))
    op = rng.choice(kinds)
    inner = random_formula(rng, depth - 1, kinds)
    return Knows(AG, inner) if op is Knows else op(inner)


@pytest.mark.parametrize("frame, systems, kinds", [
    ("T", None, (Box, Diamond)),
    ("S4", None, (Box, Diamond)),
    ("S5", None, (Box, Diamond)),
    ("D", None, (Box, Diamond)),
    ("KD45", None, (Box, Diamond)),
    ("K", None, (Obligatory, Permitted, Box)),
    ("T", {"deontic": "KD45"}, (Obligatory, Permitted, Box)),
    ("K", {"epistemic": "S5"}, (Knows, Box)),
    ("S4", {"epistemic": "S4", "deontic": "D"}, (Knows, Obligatory, Box, Diamond)),
])
def test_every_countermodel_on_random_formulas_is_a_model_of_the_frame(frame, systems, kinds):
    rng = random.Random(zlib.crc32(repr((frame, systems)).encode()))
    handed_out = 0
    for _ in range(120):
        formula = random_formula(rng, 3, kinds)
        model = check_model(formula, frame, systems)
        handed_out += model is not None
    assert handed_out >= 20     # the battery is not vacuous


def small_models(relations, letters, worlds=2):
    """EVERY model on ``worlds`` worlds with one relation per name in ``relations`` and these letters."""
    dom = range(worlds)
    cells = list(itertools.product(dom, repeat=2))
    edge_sets = [frozenset(c for k, c in enumerate(cells) if mask >> k & 1)
                 for mask in range(1 << len(cells))]
    valuations = list(itertools.product([frozenset(), frozenset({"A"})], repeat=worlds))
    for chosen in itertools.product(edge_sets, repeat=len(relations)):
        for val in valuations:
            yield type("M", (), {
                "worlds": set(dom), "relations": dict(zip(relations, chosen)),
                "valuation": {w: set(val[w]) for w in dom}})()


@pytest.mark.parametrize("frame", ["T", "S4", "S5", "D", "KD45"])
def test_no_formula_is_called_valid_that_a_two_world_model_of_the_frame_falsifies(frame):
    rng = random.Random(7)
    models = [m for m in small_models(["alethic"], ["A"]) if not frame_problems(m, {"alethic": frame})]
    for _ in range(60):
        formula = random_formula(rng, 3, (Box, Diamond))
        # only A is true somewhere in these models; B and Q are false everywhere, which is one valuation
        if any(not true_at(formula, m, 0) for m in models):
            assert modal_decide(formula, frame=frame) != "valid", formula.to_unicode_str()
