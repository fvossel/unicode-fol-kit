"""Tests for the past-tense temporal operators (Historically/Once/Previous/Since).

The four past operators are the exact duals of the future ones over the *converse*
of the one-step ``"temporal"`` relation. That gives a rigorous, self-checking
oracle: for every model ``m`` and world ``w``,

    satisfies_modal(past(φ), m, w)  ==  satisfies_modal(future(φ), reverse(m), w)

where ``past`` swaps Always→Historically, Eventually→Once, Next→Previous,
Until→Since and ``reverse`` flips every temporal edge. Since the future operators
are already tested, this validates the past implementation against them. We also
hand-check explicit linear models, parse / Unicode / LaTeX / JSON round-trips, and
that the LaTeX markers do not collide with the deontic Ⓞ/Ⓟ operators.
"""

import random

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Node, Atom, Not, And, Or, Implies,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.fol.latex_input import parse_latex

P_, Q_, R_ = Atom("P", ()), Atom("Q", ()), Atom("R", ())
_parser = MSFLParser(modal=True)


# --------------------------------------------------------------------------- #
# Parsing, Unicode / LaTeX / JSON round-trips.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("src, expect", [
    ("⒣P", Historically(P_)),
    ("⒫P", Once(P_)),
    ("⒴P", Previous(P_)),
    ("P ⒮ Q", Since(P_, Q_)),
    ("⒣(P → Q)", Historically(Implies(P_, Q_))),
    ("⒫⒣P", Once(Historically(P_))),
])
def test_parse_past_operators(src, expect):
    assert _parser.parse(src) == expect


@pytest.mark.parametrize("formula", [
    Historically(P_), Once(P_), Previous(P_), Since(P_, Q_),
    Once(Historically(Previous(P_))), And(Always(P_), Historically(P_)),
    Since(Implies(P_, Q_), Or(P_, R_)),
])
def test_unicode_roundtrip(formula):
    assert _parser.parse(formula.to_unicode_str()) == formula


@pytest.mark.parametrize("formula", [
    Historically(P_), Once(P_), Previous(P_), Since(P_, Q_),
    # Mixed with the deontic Ⓞ/Ⓟ operators, whose LaTeX is \mathsf{O}/\mathsf{P}:
    # the past markers are overlined so \overline{\mathsf{P}} ≠ \mathsf{P}.
    And(Obligatory(P_), Once(Q_)), And(Permitted(P_), Historically(Q_)),
])
def test_latex_roundtrip_no_deontic_collision(formula):
    assert parse_latex(formula.to_latex(), modal=True) == formula


@pytest.mark.parametrize("formula", [
    Historically(P_), Once(P_), Previous(P_), Since(P_, Q_),
])
def test_json_roundtrip(formula):
    assert Node.from_dict(formula.to_dict()) == formula


# --------------------------------------------------------------------------- #
# Hand-checked semantics on an explicit linear model 0 → 1 → 2, P only at 0.
# --------------------------------------------------------------------------- #

_LINEAR = KripkeModel([0, 1, 2], {"temporal": {(0, 1), (1, 2)}}, {0: {"P"}})


@pytest.mark.parametrize("formula, world, expected", [
    (Once(P_), 2, True),               # P was once true (at 0)
    (Once(P_), 0, True),               # P holds now ⇒ once (n=0)
    (Historically(P_), 2, False),      # P false at 1, 2
    (Historically(P_), 0, True),       # only past point is 0 itself, where P holds
    (Previous(P_), 1, True),           # immediate predecessor 0 has P
    (Previous(P_), 0, True),           # no predecessors ⇒ vacuously true
    (Since(Or(P_, Not(P_)), P_), 2, True),    # ⊤ since P (P held in the past)
    (Since(Q_, P_), 1, False),         # Q false now and P false now ⇒ no Since path
])
def test_linear_model_semantics(formula, world, expected):
    assert satisfies_modal(formula, _LINEAR, world) is expected


def test_yesterday_is_universal_over_predecessors():
    # Branching past: world 2 has two predecessors 0 and 1; P only at 0.
    m = KripkeModel([0, 1, 2], {"temporal": {(0, 2), (1, 2)}}, {0: {"P"}})
    assert satisfies_modal(Previous(P_), m, 2) is False     # not P at predecessor 1
    assert satisfies_modal(Once(P_), m, 2) is True          # P at predecessor 0


# --------------------------------------------------------------------------- #
# Duality oracle: past over m == future over the converse of m.
# --------------------------------------------------------------------------- #

_FUTURE_TO_PAST = {Always: Historically, Eventually: Once, Next: Previous}


def _to_past(node: Node) -> Node:
    """Map every future temporal operator in ``node`` to its past dual."""
    if isinstance(node, (Always, Eventually, Next)):
        return _FUTURE_TO_PAST[type(node)](_to_past(node.formula))
    if isinstance(node, Until):
        return Since(_to_past(node.left), _to_past(node.right))
    return node.map_children(_to_past)


def _reverse(model: KripkeModel) -> KripkeModel:
    """Return a copy of ``model`` with every temporal edge reversed."""
    rels = {name: set(edges) for name, edges in model.relations.items()}
    rels["temporal"] = {(b, a) for (a, b) in model.relation("temporal")}
    return KripkeModel(model.worlds, rels,
                       {w: set(model.atoms_true_at(w)) for w in model.worlds})


_ATOMS = [Atom("P", ()), Atom("Q", ())]


def _rand_future_formula(depth, rng):
    if depth <= 0 or (depth < 3 and rng.random() < 0.4):
        return rng.choice(_ATOMS)
    k = rng.random()
    if k < 0.18:
        return Not(_rand_future_formula(depth - 1, rng))
    if k < 0.34:
        return Always(_rand_future_formula(depth - 1, rng))
    if k < 0.50:
        return Eventually(_rand_future_formula(depth - 1, rng))
    if k < 0.62:
        return Next(_rand_future_formula(depth - 1, rng))
    if k < 0.74:
        return Until(_rand_future_formula(depth - 1, rng), _rand_future_formula(depth - 1, rng))
    if k < 0.84:
        return And(_rand_future_formula(depth - 1, rng), _rand_future_formula(depth - 1, rng))
    if k < 0.94:
        return Or(_rand_future_formula(depth - 1, rng), _rand_future_formula(depth - 1, rng))
    return Implies(_rand_future_formula(depth - 1, rng), _rand_future_formula(depth - 1, rng))


def _rand_model(rng):
    n = rng.randint(1, 4)
    worlds = list(range(n))
    edges = {(a, b) for a in worlds for b in worlds if rng.random() < 0.4}
    val = {w: {a.predicate for a in _ATOMS if rng.random() < 0.5} for w in worlds}
    return KripkeModel(worlds, {"temporal": edges}, val)


def test_past_future_duality_over_converse():
    rng = random.Random(31337)
    checks = 0
    for _ in range(300):
        fut = _rand_future_formula(3, rng)
        past = _to_past(fut)
        m = _rand_model(rng)
        rev = _reverse(m)
        for w in m.worlds:
            assert satisfies_modal(past, m, w) == satisfies_modal(fut, rev, w), (
                f"duality broke at world {w}: past={past.to_unicode_str()} "
                f"future={fut.to_unicode_str()}")
            checks += 1
    assert checks > 300


# --------------------------------------------------------------------------- #
# Sound rejection where the past operators are not (yet) handled.
# --------------------------------------------------------------------------- #

def test_modal_tableau_points_elsewhere_for_past():
    from unicode_fol_kit.atp.modal_tableau import is_modal_valid
    with pytest.raises(NotImplementedError, match="satisfies_modal|isabelle_decide_modal"):
        is_modal_valid(Historically(P_))


def test_kleene_value_rejects_past_operators():
    from unicode_fol_kit.semantics.manyvalued import kleene_value
    with pytest.raises(NotImplementedError):
        kleene_value(Once(P_), {})


def test_standard_translation_past_box_diamond():
    # Historically/Once/Previous translate to FO; Since is rejected like Until.
    from unicode_fol_kit.fol.modal_translation import standard_translation
    assert standard_translation(Historically(P_)) is not None
    assert standard_translation(Once(P_)) is not None
    assert standard_translation(Previous(P_)) is not None
    with pytest.raises(NotImplementedError, match="Until / Since"):
        standard_translation(Since(P_, Q_))
