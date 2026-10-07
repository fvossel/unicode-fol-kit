r"""The capture invariant itself: no bound variable of an image has the name of a
constant of that image.

``Variable("x0")`` and ``Constant("x0")`` are the texts ``x0`` and ``'x0'`` and two
symbols to Z3, but would be one symbol to a target that gives both one
namespace, so a quantifier that binds ``x0`` would capture an individual called
``x0`` there. Every binder of
every image — the GCI's prefix variable, the role axioms' ``x``/``y``/``z``, the
data axioms' ``x``/``v``/``w``, the sort axioms', and every MINTED ``x0``, ``x1``,
… — therefore avoids the individuals of the whole knowledge base.
``tests/test_dl_binder_capture.py`` pins the semantic consequences
(a consistent knowledge base reported inconsistent), one binder at a time; three
mutants of that avoidance still survived all of it, because each needs the individual
that would be captured to stand in a DIFFERENT conjunct than the binder:

* ``abox_to_fol``'s minted variables avoiding only the individuals of the
  assertion's own concept, not of the whole ABox;
* the domain/range FILLER minter of the role box and of the data box dropping the
  call-wide avoid set;
* the knowledge-base individual set of :func:`dl.kb_to_fol` ignoring the ABox.

So this file tests the INVARIANT, structurally: walk every formula an entry point
returns, collect the names of its bound variables (``Quantifier`` and ``Count``)
and the names of its constants, and require the two sets disjoint. Every scenario
puts the individual in one conjunct and the binder that would capture it in
another — the individuals are named like the names the translation mints
(``x0``, ``a0``) or binds (``x``, ``y``, ``v``).

The invariant is stricter than the semantics need (a binder only captures inside
its own scope), and that is the point: it holds without a case analysis of which
conjunct could see which, and it is what a writer with one namespace for
variables and constants needs to be sure ``x0`` means one thing.
"""

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit.fol.nodes import Constant, Count, Quantifier

A, B, C, D = (dl.Atomic(name) for name in "ABCD")


def _walk(nodes):
    for node in nodes:
        yield from node.walk()


def _bound_names(nodes) -> set:
    return {n.variable.name for n in _walk(nodes) if isinstance(n, (Quantifier, Count))}


def _constant_names(nodes) -> set:
    return {n.name for n in _walk(nodes) if isinstance(n, Constant)}


def _no_capture(nodes) -> None:
    nodes = list(nodes)
    clash = _bound_names(nodes) & _constant_names(nodes)
    assert not clash, (
        f"bound variable(s) {sorted(clash)} share a name with a constant of the "
        f"same image:\n  " + "\n  ".join(n.to_unicode_str() for n in nodes))


# --------------------------------------------------------------------------- #
# The scenarios: each is (TBox, ABox), built fresh. The binder and the
# individual it could capture are always in different axioms/assertions.
# --------------------------------------------------------------------------- #

def _abox_scenario():
    # a : ∃r.A mints a0 (the base letter of the individual is `a`); another
    # assertion is about an individual called a0, and a third ABox individual is
    # called like the next minted names.
    abox = (dl.ABox()
            .assert_concept("a", dl.Exists("r", A))
            .assert_concept("a0", B)
            .assert_concept("b", dl.AtLeast(2, "r", dl.ForAll("s", C)))
            .assert_role("b0", "b1", "r")
            .assert_concept("x", dl.Exists("s", D))
            .assert_concept("x0", C))
    return dl.TBox(), abox


def _tbox_scenario():
    # A ⊑ ∃r.∀s.B mints x0, x1 under the prefix variable x; other inclusions
    # name individuals called x, x0, x1 and y (nominals and value restrictions).
    tbox = (dl.TBox()
            .add(A, dl.Exists("r", dl.ForAll("s", B)))
            .add(dl.Nominal("x0"), C)
            .add(dl.HasValue("r", "x1"), D)
            .add(dl.Nominal("x"), A)
            .add(B, dl.HasValue("s", "y")))
    return tbox, dl.ABox()


def _rbox_scenario():
    # a domain filler mints x0 inside the axiom for r, a range filler mints one
    # inside the axiom for q, and a THIRD axiom's filler names the individuals
    # x0 and y0 (and the prefix variables x, y, z are individuals elsewhere).
    tbox = (dl.TBox()
            .add_role_domain("r", dl.Exists("s", D))
            .add_role_range("q", dl.ForAll("s", dl.Exists("t", C)))
            .add_role_domain("p", dl.HasValue("s", "x0"))
            .add_role_range("p", dl.Nominal("y0"))
            .add_role_domain("o", dl.Nominal("x"))
            .add_role_range("o", dl.Nominal("y"))
            .add_transitive_role("n")
            .add_role_domain("m", dl.Nominal("z"))
            .add_role_chain(["c1", "c2", "c3", "c4"], "c5"))
    return tbox, dl.ABox()


def _databox_scenario():
    tbox = (dl.TBox()
            .add_data_property_domain("d", dl.Exists("s", D))
            .add_data_property_domain("e", dl.HasValue("s", "x0"))
            .add_data_property_domain("f", dl.Nominal("v"))
            .add_data_property_domain("g", dl.Nominal("x"))
            .add_functional_data_property("d")
            .add_data_property_domain("h", dl.Nominal("w")))
    return tbox, dl.ABox().assert_data("a", "d", dl.Literal("1", "xsd:integer"))


def _knowledge_base_scenario():
    # the TBox mints x0 (a GCI under x), the ABox names an individual x0 and
    # one called x1; the role box and the data box mint under their own prefix
    # variables while the ABox names y, z, v, w, t.
    tbox = (dl.TBox()
            .add(A, dl.Exists("r", B))
            .add_role_domain("q", dl.Exists("s", C))
            .add_data_property_domain("d", dl.Exists("s", D))
            .add_data_property_range("d", dl.Datatype("xsd:integer")))
    abox = (dl.ABox()
            .assert_concept("x0", C)
            .assert_concept("x1", D)
            .assert_concept("y", A)
            .assert_concept("z", B)
            .assert_concept("v", C)
            .assert_concept("w", D)
            .assert_concept("t", A)
            .assert_concept("a", dl.Exists("r", B))
            .assert_concept("a0", dl.Exists("s", C))
            .assert_data("x", "d", dl.Literal("1", "xsd:integer")))
    return tbox, abox


SCENARIOS = [_abox_scenario, _tbox_scenario, _rbox_scenario, _databox_scenario,
             _knowledge_base_scenario]
IDS = ["abox", "tbox", "rbox", "databox", "knowledge-base"]


# --------------------------------------------------------------------------- #
# The invariant, over every entry point that renders a part of the image.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("scenario", SCENARIOS, ids=IDS)
def test_abox_to_fol_binds_no_name_of_the_abox_it_renders(scenario):
    # a : ∃r.A mints a0 while a0 : B is another assertion; the minted variable
    # must avoid every individual of the WHOLE ABox, not just the assertion's own.
    _, abox = scenario()
    _no_capture([dl.abox_to_fol(abox)])


@pytest.mark.parametrize("scenario", SCENARIOS, ids=IDS)
def test_tbox_to_fol_binds_no_name_of_the_tbox_it_renders(scenario):
    tbox, _ = scenario()
    _no_capture([dl.tbox_to_fol(tbox, concept_inclusions_only=True)])


@pytest.mark.parametrize("scenario", SCENARIOS, ids=IDS)
def test_rbox_to_fol_binds_no_name_of_the_tbox_it_renders(scenario):
    tbox, _ = scenario()
    _no_capture([dl.rbox_to_fol(tbox)])


@pytest.mark.parametrize("scenario", SCENARIOS, ids=IDS)
def test_databox_to_fol_binds_no_name_of_the_tbox_it_renders(scenario):
    tbox, _ = scenario()
    _no_capture([dl.databox_to_fol(tbox)])


@pytest.mark.parametrize("scenario", SCENARIOS, ids=IDS)
@pytest.mark.parametrize("separation", ["two-sorted", "data-lattice", "none"])
def test_kb_to_fol_binds_no_name_of_the_knowledge_base_it_renders(scenario, separation):
    # Every formula the bundle hands a prover: the knowledge base, each of its
    # halves, every side axiom (the role box, the data box, the sort axioms).
    tbox, abox = scenario()
    kb = dl.kb_to_fol(tbox, abox, separation=separation)
    _no_capture([kb.formula, kb.tbox, kb.abox, *kb.axioms])


@pytest.mark.parametrize("scenario", SCENARIOS, ids=IDS)
def test_the_goal_builders_bind_no_name_of_the_bundle(scenario):
    # The same invariant for the goals the bundle builds, over the individuals of
    # the bundle AND of the question.
    tbox, abox = scenario()
    concept = dl.And(dl.Exists("r", A), dl.Exists("s", dl.ForAll("r", B)))
    kb = dl.kb_to_fol(tbox, abox, query=[concept, dl.Nominal("x1"), dl.Nominal("y0")])
    sub, sup = concept, dl.Exists("r", dl.Nominal("x0"))
    _no_capture([kb.formula, *kb.axioms, kb.subsumption_goal(sub, sup),
                 kb.unsatisfiability_goal(sub), kb.instance_goal("a0", concept),
                 kb.instance_goal("zz", concept)])


# --------------------------------------------------------------------------- #
# The invariant is not vacuous: each scenario really has a binder that the
# unprotected translation would give the individual's name.
# --------------------------------------------------------------------------- #

def test_the_scenarios_name_what_the_translation_mints_and_binds():
    # a minted x0 / a0, the prefix variables x, y, v, w: all of them are also
    # individuals somewhere in the scenario, in another axiom.
    _, abox = _abox_scenario()
    assert {"a0", "x0", "b0", "x"} <= {i for i, _c in abox.concept_assertions} | {
        a for a, _b, _r in abox.role_assertions}
    tbox, _ = _tbox_scenario()
    kb = dl.kb_to_fol(tbox)
    assert {"x", "x0", "x1", "y"} <= _constant_names([kb.formula])
    assert _bound_names([kb.formula]) and not (
        _bound_names([kb.formula]) & _constant_names([kb.formula]))
