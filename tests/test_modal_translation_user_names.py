"""A user's variable or constant named like a name the modal translations mint keeps its meaning.

The standard translation binds world variables ``w0``, ``w1``, … and the hybrid routes close the
image over the current world ``w``. A formula whose atoms carry a variable called ``w0`` (``□P(w0)``:
the same unknown individual at every successor) must not have that variable read as the bound
world: ``□P(w0)`` is ``∀w1 (R(w, w1) → P(w0, w1))``, and the individual ``w0`` is the same one
in every atom of the formula.

The reference semantics is a brute-force Kripke check written here, independent of every translation:
every model over 2 worlds and 2 individuals, a rigid value for every constant and every free
variable (a free variable is a parameter, one element for the whole formula), a predicate extension at
every world, and the frame conditions of the system tested. A route that PROVES a formula that has a
countermodel is wrong; a route must give the same verdict for a formula and for the same formula with
every variable and constant renamed to a name no translation mints.
"""

import random
from itertools import product

import pytest

from unicode_fol_kit.atp import resolution
from unicode_fol_kit.atp.logic_backends import HybridBackend
from unicode_fol_kit.fol import modal_translation as mt
from unicode_fol_kit.fol import qml
from unicode_fol_kit.fol.nodes import (
    And, Atom, Box, Constant, Diamond, Iff, Implies, Not, Or, Quantifier, Variable, free_variables,
)

V, C = Variable, Constant


def P(*terms):
    return Atom("P", list(terms))


def Q(*terms):
    return Atom("Q", list(terms))


# --------------------------------------------------------------------------- #
# the reference: a brute-force Kripke check
# --------------------------------------------------------------------------- #

FRAME_CONDITIONS = {"K": (), "T": ("refl",), "S5": ("refl", "trans", "sym")}


def _frame_ok(relation, worlds, conditions):
    for condition in conditions:
        if condition == "refl" and not all((w, w) in relation for w in range(worlds)):
            return False
        if condition == "sym" and not all((v, w) in relation for (w, v) in relation):
            return False
        if condition == "trans" and not all(
                (w, u) in relation for (w, v) in relation for (v2, u) in relation if v2 == v):
            return False
    return True


def _relations(worlds, conditions):
    pairs = [(a, b) for a in range(worlds) for b in range(worlds)]
    for bits in product((False, True), repeat=len(pairs)):
        relation = frozenset(p for p, bit in zip(pairs, bits) if bit)
        if _frame_ok(relation, worlds, conditions):
            yield relation


def _symbols(formula):
    predicates, constants, free = {}, set(), set()

    def walk(node, bound):
        if isinstance(node, Atom):
            predicates[node.predicate] = len(node.args)
            for arg in node.args:
                walk(arg, bound)
        elif isinstance(node, Variable):
            if node.name not in bound:
                free.add(node.name)
        elif isinstance(node, Constant):
            constants.add(node.name)
        elif isinstance(node, Quantifier):
            walk(node.formula, bound | {node.variable.name})
        else:
            for child in node._child_nodes():
                walk(child, bound)

    walk(formula, frozenset())
    return predicates, sorted(constants), sorted(free)


def _holds(formula, world, model, env):
    relation, extension, constants = model
    if isinstance(formula, Atom):
        args = tuple(env[a.name] if isinstance(a, Variable) else constants[a.name]
                     for a in formula.args)
        return args in extension[(formula.predicate, world)]
    if isinstance(formula, Not):
        return not _holds(formula.formula, world, model, env)
    if isinstance(formula, And):
        return _holds(formula.left, world, model, env) and _holds(formula.right, world, model, env)
    if isinstance(formula, Or):
        return _holds(formula.left, world, model, env) or _holds(formula.right, world, model, env)
    if isinstance(formula, Implies):
        return (not _holds(formula.left, world, model, env)) or _holds(formula.right, world, model, env)
    if isinstance(formula, Iff):
        return _holds(formula.left, world, model, env) == _holds(formula.right, world, model, env)
    if isinstance(formula, Box):
        return all(_holds(formula.formula, v, model, env) for (u, v) in relation if u == world)
    if isinstance(formula, Diamond):
        return any(_holds(formula.formula, v, model, env) for (u, v) in relation if u == world)
    if isinstance(formula, Quantifier):
        # constant domain: every individual exists at every world
        values = (_holds(formula.formula, world, model, {**env, formula.variable.name: d})
                  for d in range(2))
        return all(values) if formula.type == "∀" else any(values)
    raise TypeError(type(formula).__name__)


def has_countermodel(formula, frame="K", worlds=2, individuals=2):
    """Whether some model over ``worlds`` worlds and ``individuals`` individuals falsifies ``formula``."""
    predicates, constants, free = _symbols(formula)
    cells = [(name, w) for name in sorted(predicates) for w in range(worlds)]
    tuples = {name: list(product(range(individuals), repeat=arity))
              for name, arity in predicates.items()}
    per_cell = [[frozenset(t for t, bit in zip(tuples[name], bits) if bit)
                 for bits in product((False, True), repeat=len(tuples[name]))]
                for (name, _w) in cells]
    for relation in _relations(worlds, FRAME_CONDITIONS[frame]):
        for chosen in product(*per_cell):
            extension = dict(zip(cells, chosen))
            for values in product(range(individuals), repeat=len(constants)):
                model = (relation, extension, dict(zip(constants, values)))
                for assignment in product(range(individuals), repeat=len(free)):
                    env = dict(zip(free, assignment))
                    for world in range(worlds):
                        if not _holds(formula, world, model, env):
                            return True
    return False


# --------------------------------------------------------------------------- #
# the image of a formula with a variable named like a minted world variable
# --------------------------------------------------------------------------- #

def _text(node):
    return node.to_unicode_str()


def test_a_variable_named_like_a_minted_world_variable_stays_outside_the_bound_world():
    # □P(w0) says: P holds of the individual w0 at every successor of w. The bound world is w1.
    image = mt.standard_translation(Box(P(V("w0"))))
    assert _text(image) == "∀w1 (R(w, w1) → P(w0, w1))"
    assert {v.name for v in free_variables(image)} == {"w", "w0"}


def test_every_modality_binds_a_world_clear_of_every_variable_of_the_formula():
    # nested boxes over atoms of w0, w1, w2: the bound worlds are the first names that no atom uses
    formula = Box(And(P(V("w0")), Box(And(P(V("w1")), P(V("w2"))))))
    image = mt.standard_translation(formula)
    bound = {n.variable.name for n in image.walk() if isinstance(n, Quantifier)}
    assert bound == {"w3", "w4"}
    assert {v.name for v in free_variables(image)} == {"w", "w0", "w1", "w2"}


def test_a_formula_without_such_a_variable_translates_as_before():
    assert _text(mt.standard_translation(Box(Box(Q(C("alice")))))) == \
        "∀w0 (R(w, w0) → ∀w1 (R(w0, w1) → Q(alice, w1)))"
    assert _text(mt.standard_translation(Diamond(P(V("x"))))) == "∃w0 (R(w, w0) ∧ P(x, w0))"


def test_a_variable_named_like_the_current_world_is_another_variable_in_the_image():
    # P(w): the individual w at the world w. They are two symbols.
    image = mt.standard_translation(P(V("w")))
    assert _text(image) == "P(x0, w)"
    # one renaming for the whole formula: both atoms mention the same individual
    both = mt.standard_translation(And(P(V("w")), Diamond(Q(V("w")))))
    assert _text(both) == "P(x0, w) ∧ ∃w0 (R(w, w0) ∧ Q(x0, w0))"


def test_the_renamed_variable_keeps_clear_of_the_variables_of_the_formula_and_of_avoid():
    formula = And(P(V("w")), Q(V("x0")))
    assert _text(mt.standard_translation(formula)) == "P(x1, w) ∧ Q(x0, w)"
    assert _text(mt.standard_translation(P(V("w")), avoid=["x0", "x1"])) == "P(x2, w)"


def test_a_variable_named_like_a_chosen_current_world_is_renamed_too():
    image = mt.standard_translation(Box(P(V("u"))), world="u")
    assert _text(image) == "∀w0 (R(u, w0) → P(x0, w0))"


def test_a_renamed_variable_is_renamed_inside_a_function_term_too():
    from unicode_fol_kit.fol.nodes import Function
    image = mt.standard_translation(P(Function("f", [V("w")])))
    assert _text(image) == "P(f(x0), w)"


def test_a_constant_named_like_a_world_variable_is_not_a_variable_of_the_image():
    # a constant and a variable of one spelling are two symbols to the kit, but a target that
    # has one namespace for both would read them as one: the bound world is another name
    image = mt.standard_translation(Box(P(C("w0"))))
    assert {n.name for n in image.walk() if isinstance(n, Constant)} == {"w0"}
    assert {v.name for v in free_variables(image)} == {"w"}
    assert [n.variable.name for n in image.walk() if isinstance(n, Quantifier)] == ["w1"]


def test_a_predicate_or_a_nominal_named_like_a_world_variable_is_not_reused_as_one():
    from unicode_fol_kit.fol.nodes import Nominal
    image = mt.standard_translation(Box(Atom("w0", [])))
    assert [n.variable.name for n in image.walk() if isinstance(n, Quantifier)] == ["w1"]
    nominal = mt.standard_translation(Box(Nominal("w0")))
    assert [n.variable.name for n in nominal.walk() if isinstance(n, Quantifier)] == ["w1"]


def test_the_names_are_compared_with_their_case_folded():
    # TPTP and Prover9 read W0 and w0 as one word
    image = mt.standard_translation(Box(P(V("W0"))))
    assert [n.variable.name for n in image.walk() if isinstance(n, Quantifier)] == ["w1"]
    # and a variable W is the world w to such a target: it is renamed
    assert _text(mt.standard_translation(P(V("W")))) == "P(x0, w)"


# --------------------------------------------------------------------------- #
# verdicts of the hybrid routes and of the modal route of resolution
# --------------------------------------------------------------------------- #

def _hybrid_status(formula, frame="K"):
    return HybridBackend().decide(formula, [], timeout=8000, frame=frame).status


def test_box_of_a_variable_named_w0_implies_itself():
    # φ → φ is valid whatever φ is; a captured w0 made the two boxes different statements
    formula = Implies(Box(P(V("w0"))), Box(P(V("w0"))))
    assert mt.hybrid_is_valid(formula, "K") is True
    assert _hybrid_status(formula) == "proved"
    assert resolution.prove([], formula, max_steps=20000, timeout=8000) is True


def test_the_hybrid_backend_does_not_prove_what_has_a_countermodel_through_a_captured_variable():
    # □P(a) ∧ P(a) → □(Q(b) → P(b)) with a = w0 and b = w1 two unknown individuals is NOT valid:
    # worlds {0, 1}, R = {(0, 1)}, individuals {0, 1}, a = 0, b = 1; P holds of 0 at both worlds,
    # Q holds of 1 at world 1 and P does not hold of 1 there. At world 0 the antecedent is true
    # (P(0) at 0 and at the successor 1) and the successor 1 falsifies Q(1) → P(1).
    formula = Implies(And(Box(P(V("w0"))), P(V("w0"))),
                      Box(Implies(Q(V("w1")), P(V("w1")))))
    assert has_countermodel(formula, "K")
    assert _hybrid_status(formula) == "refuted"
    assert mt.hybrid_is_valid(formula, "K") is False


def test_the_duality_of_box_and_diamond_holds_for_a_variable_named_like_a_minted_world():
    formula = Iff(Box(P(V("w1"))), Not(Diamond(Not(P(V("w1"))))))
    assert not has_countermodel(formula, "K")
    assert _hybrid_status(formula) == "proved"
    assert mt.hybrid_is_valid(formula, "K") is True


@pytest.mark.parametrize("frame", ["K", "T", "S5"])
def test_reflexivity_is_read_through_a_variable_named_w(frame):
    # □P(w) → P(w) is valid exactly when the frame is reflexive (T, S5), for the individual w
    formula = Implies(Box(P(V("w"))), P(V("w")))
    expected = frame != "K"
    assert (not has_countermodel(formula, frame)) is expected
    assert (_hybrid_status(formula, frame) == "proved") is expected
    assert mt.hybrid_is_valid(formula, frame) is expected


# --------------------------------------------------------------------------- #
# generated formulas: the same verdict whatever the user symbols are called
# --------------------------------------------------------------------------- #

CLASH_VARIABLES = ["w", "w0", "w1", "v0", "x0"]
CLASH_CONSTANTS = ["w", "w0", "v0"]


def _generate(rng, depth, quantifiers):
    """An abstract formula as a nested tuple (names are filled in by :func:`_build`)."""
    if depth == 0 or rng.random() < 0.3:
        term = (("var", rng.choice(CLASH_VARIABLES)) if rng.random() < 0.7
                else ("const", rng.choice(CLASH_CONSTANTS)))
        return ("atom", rng.choice(["P", "Q"]), term)
    kinds = ["not", "and", "imp", "iff", "box", "dia", "box", "dia"]
    if quantifiers:
        kinds += ["all", "ex"]
    kind = rng.choice(kinds)
    if kind in ("not", "box", "dia"):
        return (kind, _generate(rng, depth - 1, quantifiers))
    if kind in ("and", "imp", "iff"):
        return (kind, _generate(rng, depth - 1, quantifiers), _generate(rng, depth - 1, quantifiers))
    return (kind, rng.choice(CLASH_VARIABLES), _generate(rng, depth - 1, quantifiers))


def _schema(rng, quantifiers):
    """A shape that is valid in K whatever its parts are, filled with generated parts."""
    a, b = _generate(rng, 1, quantifiers), _generate(rng, 1, quantifiers)
    shape = rng.choice(["id", "dist", "conj", "dual", "k", "contra"])
    if shape == "id":
        return ("imp", ("box", a), ("box", a))
    if shape == "dist":
        return ("imp", ("box", ("imp", a, b)), ("imp", ("box", a), ("box", b)))
    if shape == "conj":
        return ("imp", ("and", ("box", a), ("box", b)), ("box", ("and", a, b)))
    if shape == "dual":
        return ("iff", ("box", a), ("not", ("dia", ("not", a))))
    if shape == "k":
        return ("imp", ("and", ("box", a), ("dia", b)), ("dia", ("and", a, b)))
    return ("imp", ("imp", a, b), ("imp", ("not", b), ("not", a)))


def _names(tree, found=None):
    found = found if found is not None else {"var": set(), "const": set()}
    if tree[0] == "atom":
        found[tree[2][0]].add(tree[2][1])
    elif tree[0] in ("all", "ex"):
        found["var"].add(tree[1])
        _names(tree[2], found)
    else:
        for part in tree[1:]:
            _names(part, found)
    return found


def _build(tree, variable, constant):
    tag = tree[0]
    if tag == "atom":
        kind, name = tree[2]
        return Atom(tree[1], [V(variable(name)) if kind == "var" else C(constant(name))])
    if tag in ("not", "box", "dia"):
        cls = {"not": Not, "box": Box, "dia": Diamond}[tag]
        return cls(_build(tree[1], variable, constant))
    if tag in ("and", "imp", "iff"):
        cls = {"and": And, "imp": Implies, "iff": Iff}[tag]
        return cls(_build(tree[1], variable, constant), _build(tree[2], variable, constant))
    return Quantifier("∀" if tag == "all" else "∃", V(variable(tree[1])),
                      _build(tree[2], variable, constant))


def _pairs(count, seed, quantifiers):
    """``count`` formulas with clashing names, each with its renamed twin, and its abstract form."""
    rng = random.Random(seed)
    pairs = []
    while len(pairs) < count:
        tree = _schema(rng, quantifiers) if rng.random() < 0.75 else _generate(rng, 3, quantifiers)
        names = _names(tree)
        if len(names["var"]) + len(names["const"]) > 3:
            continue
        variables = {n: f"ua{i}" for i, n in enumerate(sorted(names["var"]))}
        constants = {n: f"kb{i}" for i, n in enumerate(sorted(names["const"]))}
        pairs.append((_build(tree, lambda n: n, lambda n: n),
                      _build(tree, variables.get, constants.get)))
    return pairs


MODAL_PAIRS = _pairs(40, seed=20261005, quantifiers=False)
QUANTIFIED_PAIRS = _pairs(24, seed=20261006, quantifiers=True)


@pytest.mark.parametrize("frame", ["K", "T"])
def test_the_hybrid_backend_gives_one_verdict_for_a_formula_and_its_renamed_twin(frame):
    proved = 0
    for clashing, clean in MODAL_PAIRS:
        verdict = _hybrid_status(clashing, frame)
        assert verdict == _hybrid_status(clean, frame), _text(clashing)
        if verdict == "proved":
            proved += 1
            assert not has_countermodel(clashing, frame), _text(clashing)
    assert proved >= 15


def test_the_hybrid_check_and_the_hybrid_backend_agree_on_generated_formulas():
    for clashing, _clean in MODAL_PAIRS:
        assert mt.hybrid_is_valid(clashing, "K") == (_hybrid_status(clashing) == "proved"), \
            _text(clashing)


def test_the_modal_route_of_resolution_proves_each_valid_formula_whatever_its_names():
    # the formulas below are valid (the hybrid route proves the renamed twin); resolution is not
    # complete within its budget, so the check is: whatever it proves for the renamed twin it
    # proves with the clashing names too, and what it proves has no countermodel
    valid = [(clashing, clean) for clashing, clean in MODAL_PAIRS if _hybrid_status(clean) == "proved"]
    twins_proved = 0
    for clashing, clean in valid[:16]:
        if resolution.prove([], clean, max_steps=3000, timeout=20000):
            twins_proved += 1
            assert resolution.prove([], clashing, max_steps=3000, timeout=20000), _text(clashing)
    assert twins_proved >= 6


@pytest.mark.parametrize("frame", ["K", "T"])
def test_qml_gives_one_verdict_for_a_formula_and_its_renamed_twin(frame):
    proved = 0
    for clashing, clean in QUANTIFIED_PAIRS:
        verdict = qml.qml_is_valid(clashing, mode="constant", frame=frame, timeout=8000)
        assert verdict == qml.qml_is_valid(clean, mode="constant", frame=frame, timeout=8000), \
            _text(clashing)
        if verdict:
            proved += 1
            assert not has_countermodel(clashing, frame), _text(clashing)
    assert proved >= 8


# --------------------------------------------------------------------------- #
# quantified formulas: a bound variable named like a world variable
# --------------------------------------------------------------------------- #

def test_a_quantifier_over_w_binds_the_individual_and_not_the_world():
    # ∀w □P(w) → □P(w) ... the bound w is an individual; the formula is valid in K (constant domain)
    formula = Implies(Quantifier("∀", V("w"), Box(P(V("w")))), Box(P(C("c"))))
    assert not has_countermodel(formula, "K")
    assert qml.qml_is_valid(formula, mode="constant", frame="K", timeout=8000)
    # and ∀w □P(w) → P(w) with the same bound variable is the reflexivity statement, valid in T only
    needs_reflexivity = Implies(Quantifier("∀", V("w"), Box(P(V("w")))),
                                Quantifier("∀", V("w"), P(V("w"))))
    assert has_countermodel(needs_reflexivity, "K")
    assert not has_countermodel(needs_reflexivity, "T")
    assert not qml.qml_is_valid(needs_reflexivity, mode="constant", frame="K", timeout=8000)
    assert qml.qml_is_valid(needs_reflexivity, mode="constant", frame="T", timeout=8000)


def test_the_world_variable_of_the_quantified_image_is_clear_of_every_variable_of_the_formula():
    formula = Quantifier("∀", V("w"), Quantifier("∃", V("w0"), Box(Atom("S", [V("w"), V("w0")]))))
    # the current world is w1 (w is an individual), the world bound by the box is w2 (w0 is one too)
    assert _text(qml.qml_translate(formula)) == (
        "∀w (Object(w) → ∃w0 (Object(w0) ∧ ∀w2 (World(w2) ∧ R(w1, w2) → S(w, w0, w2))))")
    assert qml.qml_is_valid(Implies(formula, formula), mode="constant", frame="K", timeout=8000)
