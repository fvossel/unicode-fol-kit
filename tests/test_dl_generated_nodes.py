r"""Whether a tableau node is generated or named is a property of the node, never of its name.

The tableau names the witnesses it creates for ``∃`` and ``≥`` restrictions, and it
treats a generated node differently from a named individual: only a generated node may
be blocked, and only a generated node may block. It used to tell the two apart by the
SPELLING of the name (a prefix), so an individual of the knowledge base that was called
like a witness was one: the first ``∃`` witness WAS the individual (their labels were
joined, and a clash between them was reported), and an individual with that prefix could
be blocked by another, so that its existential was never expanded.

A generated node is now an object of its own kind that equals no string, so a knowledge
base may call its individuals anything at all. Expectations here are derived by hand:

* a countermodel is written out as a concrete structure and every assertion is checked
  against it in the test itself;
* an inconsistency is a short proof in a comment, which does not mention a name;
* the metamorphic test renames the individuals of random knowledge bases and requires
  the same verdicts: no verdict may depend on how an individual is spelled;
* the differential asks the same questions of the FOL image (``dl.kb_to_fol``) on Z3.
  A disagreement "satisfiable against unsatisfiable" is a wrong verdict; exhausting the
  step budget, or Z3 not deciding within its budget, is neither.
"""

import random

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit import api
from unicode_fol_kit.dl import tableau
from unicode_fol_kit.fol.nodes import Not as FNot

A, B = dl.Atomic("A"), dl.Atomic("B")

#: Individual names that look like something the tableau or the FOL image makes up
#: (``_x<n>`` for a witness, ``x0`` / ``y1`` for a bound variable, ``_root`` for the
#: anonymous node, ``_probe`` for the external route's probe) or that are the name of a
#: concept or a role (``A``, ``r``).
NODE_LIKE_NAMES = ["_x1", "_x2", "_x3", "_x10", "_x0", "_x", "_x1a", "x0", "y1", "_root",
                   "_probe", "A", "r", "_x_1", "é_x1"]


# --------------------------------------------------------------------------- #
# What a witness is and is not.
# --------------------------------------------------------------------------- #

def test_a_generated_node_equals_no_name():
    branch = tableau._Branch()
    named = [f"_x{n}" for n in range(0, 12)] + ["", "x", "_root", "<generated node 1>"]
    for name in named:
        branch.add_node(name)
    generated = [branch.fresh() for _ in range(12)]
    for node in generated:
        assert all(node != name and name != node for name in named)
        assert node not in named
    assert len(set(generated)) == 12
    assert len(branch.order) == len(named) + 12 and len(branch.label) == len(named) + 12


def test_a_generated_node_is_blocked_by_an_earlier_generated_node_only():
    branch = tableau._Branch()
    for name in ("_x1", "_x2", "p"):
        branch.add_node(name)
        branch.label[name].update({A, B})       # named nodes carry the biggest labels
    first, second = branch.fresh(), branch.fresh()
    branch.label[first].add(A)
    branch.label[second].add(A)
    # a NAMED node, whatever its name and its label, neither is blocked nor blocks
    assert not any(tableau._blocked(branch, name) for name in ("_x1", "_x2", "p"))
    assert tableau._blocked(branch, first) is False       # nothing generated before it
    assert tableau._blocked(branch, second) is True       # {A} ⊆ {A}, generated before it


def test_the_node_kept_by_a_merge_is_the_named_one_whatever_the_names():
    branch = tableau._Branch()
    branch.add_node("_x1")
    branch.add_node("b")
    witness = branch.fresh()
    # a generated node is always the one that goes, in either argument order
    assert tableau._merge_order(branch, "_x1", witness) == ("_x1", witness)
    assert tableau._merge_order(branch, witness, "_x1") == ("_x1", witness)
    assert tableau._merge_order(branch, "b", witness) == ("b", witness)
    # two named nodes: the one that was added first is kept, "_x1" or not
    assert tableau._merge_order(branch, "_x1", "b") == ("_x1", "b")
    assert tableau._merge_order(branch, "b", "_x1") == ("_x1", "b")


# --------------------------------------------------------------------------- #
# Hand-derived knowledge bases.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", NODE_LIKE_NAMES)
def test_an_individual_named_like_a_witness_is_not_the_witness_of_an_existential(name):
    # ind : ∃r.A ;  name : ¬A.  Consistent, with the structure
    #   universe {0, 1};  ind ↦ 0, name ↦ 0;  A = {1};  r = {(0, 1)}
    # (no unique name assumption: two elements would do as well).
    universe = {0, 1}
    element = {"ind": 0, name: 0}
    extension_of_a = {1}
    r = {(0, 1)}
    assert any((element["ind"], d) in r and d in extension_of_a for d in universe)   # ind : ∃r.A
    assert element[name] not in extension_of_a                                       # name : ¬A
    abox = dl.ABox().assert_concept("ind", dl.Exists("r", A)).assert_concept(name, dl.Not(A))
    assert dl.abox_consistent(abox) is True
    # in that structure B is empty, so nothing forces ind into B: it is not entailed,
    # and no individual is retrieved
    assert dl.instance_check(abox, "ind", B) is False
    assert dl.instance_retrieval(abox, B) == set()
    # what IS stated is still entailed
    assert dl.instance_check(abox, "ind", dl.Exists("r", A)) is True
    assert dl.instance_check(abox, name, dl.Not(A)) is True


@pytest.mark.parametrize("name", NODE_LIKE_NAMES)
def test_individuals_named_like_the_witnesses_of_a_number_restriction_are_not_them(name):
    # ind : ≥2 r.A ;  name : ¬A ;  other : ¬A.  Consistent, with
    #   universe {0, 1, 2, 3, 4};  ind ↦ 0, name ↦ 1, other ↦ 2;  A = {3, 4};
    #   r = {(0, 3), (0, 4)}:  ind has two distinct r-successors in A, and neither
    #   named individual is in A.
    element = {"ind": 0, name: 1, "other": 2}
    extension_of_a = {3, 4}
    r = {(0, 3), (0, 4)}
    assert len({d for (s, d) in r if s == element["ind"] and d in extension_of_a}) >= 2
    assert element[name] not in extension_of_a and element["other"] not in extension_of_a
    abox = (dl.ABox().assert_concept("ind", dl.AtLeast(2, "r", A))
            .assert_concept(name, dl.Not(A)).assert_concept("other", dl.Not(A)))
    assert dl.abox_consistent(abox) is True
    assert dl.instance_check(abox, "ind", B) is False


@pytest.mark.parametrize("first, second", [
    ("p1", "p2"), ("_xa", "_xb"), ("_x1", "_x2"), ("_x2", "_x1"), ("_x10", "x0"),
    ("pa", "_xb"), ("_xa", "pb"), ("A", "r"), ("_root", "_x1"),
])
def test_an_individual_named_like_a_witness_is_never_blocked(first, second):
    # Functional(r);  first : ∃r.A ;  second : ∃r.A ;  r(second, c) ;  c : ¬A.
    # Inconsistent, whatever the individuals are called: r is functional and
    # r(second, c), so c is the only r-successor of `second`; `second : ∃r.A` needs
    # an r-successor in A, which can only be c, but c : ¬A.
    tbox = dl.TBox().add_functional_role("r")
    abox = (dl.ABox().assert_concept(first, dl.Exists("r", A))
            .assert_concept(second, dl.Exists("r", A))
            .assert_role(second, "c", "r").assert_concept("c", dl.Not(A)))
    assert dl.abox_consistent(abox, tbox) is False
    # and, without the contradicting c, it is consistent: universe {0, 1},
    # first ↦ 0, second ↦ 0, r = {(0, 1)}, A = {1}
    relaxed = (dl.ABox().assert_concept(first, dl.Exists("r", A))
               .assert_concept(second, dl.Exists("r", A)).assert_role(second, "c", "r"))
    assert dl.abox_consistent(relaxed, tbox) is True


def test_an_owl_document_with_an_individual_named_like_a_witness_is_consistent():
    # The Functional-Style reader takes the bare word _x1 for an individual.
    text = ("Ontology(Declaration(Class(A)) Declaration(ObjectProperty(r)) "
            "ClassAssertion(ObjectSomeValuesFrom(r A) a) "
            "ClassAssertion(ObjectComplementOf(A) _x1))")
    tbox, abox = dl.parse_owl_functional(text)
    assert {individual for individual, _ in abox.concept_assertions} == {"a", "_x1"}
    # the structure of the test above: a ↦ 0, _x1 ↦ 0, A = {1}, r = {(0, 1)}
    assert dl.abox_consistent(abox, tbox) is True
    assert dl.instance_retrieval(abox, B, tbox) == set()


def test_the_anonymous_root_of_a_satisfiability_question_is_not_blocked_by_a_witness():
    # ∃r.(A ⊓ ∃r.A) ⊓ ∃r.A: a root with two successors; satisfiable (universe {0, 1, 2},
    # root ↦ 0, r = {(0, 1), (1, 2)}, A = {1, 2}). The second successor's label {A} is
    # contained in the first one's, which is the case blocking exists for.
    concept = dl.And(dl.Exists("r", dl.And(A, dl.Exists("r", A))), dl.Exists("r", A))
    assert dl.concept_satisfiable(concept) is True
    # ... and ∃r.A ⊓ ∀r.¬A is not: the one successor would be in A and not in A
    assert dl.concept_satisfiable(dl.And(dl.Exists("r", A), dl.ForAll("r", dl.Not(A)))) is False


# --------------------------------------------------------------------------- #
# Metamorphic: renaming the individuals changes no verdict.
# --------------------------------------------------------------------------- #

PLAIN_NAMES = ["i1", "i2", "i3", "i4"]
RENAMED = ["_x1", "_x2", "_x10", "x0"]
RENAMED_LIKE_VOCABULARY = ["A", "r", "_root", "y1"]


def _concept(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        k = rng.random()
        if k < 0.65:
            return rng.choice((A, B))
        return dl.Not(rng.choice((A, B))) if k < 0.9 else dl.Top()
    k = rng.random()
    role = rng.choice(("r", "s"))
    if k < 0.14:
        return dl.And(_concept(rng, depth - 1), _concept(rng, depth - 1))
    if k < 0.26:
        return dl.Or(_concept(rng, depth - 1), _concept(rng, depth - 1))
    if k < 0.58:
        return dl.Exists(role, _concept(rng, depth - 1))
    if k < 0.72:
        return dl.ForAll(role, _concept(rng, depth - 1))
    if k < 0.84:
        return dl.AtLeast(rng.choice((1, 2)), role, _concept(rng, depth - 1))
    return dl.AtMost(rng.choice((0, 1, 2)), role, _concept(rng, depth - 1))


def _knowledge_base(rng, names):
    """A knowledge base over ``names``; the same ``rng`` state gives the same one up to
    the choice of names (the names are only ever picked by index)."""
    tbox, abox = dl.TBox(), dl.ABox()
    for _ in range(rng.choice((0, 0, 1))):
        tbox.add(_concept(rng, 1), _concept(rng, 2))
    if rng.random() < 0.35:
        tbox.add_functional_role(rng.choice(("r", "s")))
    if rng.random() < 0.2:
        tbox.add_role_inclusion("r", "s")
    for _ in range(rng.choice((2, 3, 4))):
        abox.assert_concept(names[rng.randrange(len(names))], _concept(rng, 2))
    for _ in range(rng.choice((0, 1, 2, 3))):
        abox.assert_role(names[rng.randrange(len(names))], names[rng.randrange(len(names))],
                         rng.choice(("r", "s")))
    if rng.random() < 0.25:
        abox.assert_same(names[rng.randrange(len(names))], names[rng.randrange(len(names))])
    if rng.random() < 0.25:
        abox.assert_distinct(names[rng.randrange(len(names))], names[rng.randrange(len(names))])
    if rng.random() < 0.2:
        abox.assert_negative_role(names[rng.randrange(len(names))],
                                  names[rng.randrange(len(names))], rng.choice(("r", "s")))
    probe_individual = names[rng.randrange(len(names))]
    return tbox, abox, probe_individual, _concept(rng, 2)


def _verdict(function, *args):
    try:
        return function(*args)
    except RuntimeError as error:
        assert "step budget" in str(error)
        return None                           # exhausting the budget is not a verdict


@pytest.mark.parametrize("renamed", [RENAMED, RENAMED_LIKE_VOCABULARY],
                         ids=["witness-like", "vocabulary-like"])
def test_no_verdict_depends_on_how_an_individual_is_spelled(renamed, monkeypatch):
    monkeypatch.setattr(tableau, "MAX_STEPS", 3000)
    compared = 0
    for seed in range(100):
        plain = _knowledge_base(random.Random(seed), PLAIN_NAMES)
        other = _knowledge_base(random.Random(seed), renamed)
        (tbox, abox, individual, query), (tbox2, abox2, individual2, query2) = plain, other
        assert query == query2 and tbox.inclusions == tbox2.inclusions
        pairs = [(dl.abox_consistent, (abox, tbox), (abox2, tbox2)),
                 (dl.instance_check, (abox, individual, query, tbox),
                  (abox2, individual2, query2, tbox2))]
        for function, plain_args, other_args in pairs:
            expected, got = _verdict(function, *plain_args), _verdict(function, *other_args)
            if expected is None or got is None:
                continue
            compared += 1
            assert got is expected, (seed, function.__name__, repr(abox), repr(abox2))
    assert compared > 150

# --------------------------------------------------------------------------- #
# Differential: the tableau against the FOL image on Z3.
# --------------------------------------------------------------------------- #

#: Individual names of the differential: witness-like (``_x1``), variable-like
#: (``x0``, ``y1``), vocabulary-like (``A``, ``r``) and the anonymous node's (``_root``).
FOL_NAMES = ["_x1", "_x2", "_x10", "x0", "y1", "A", "r", "a", "_root", "b"]
TIMEOUT_MS = 20000


def _fol_concept(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        k = rng.random()
        if k < 0.65:
            return rng.choice((A, B))
        if k < 0.9:
            return dl.Not(rng.choice((A, B)))
        return dl.Top()
    k = rng.random()
    if k < 0.14:
        return dl.And(_fol_concept(rng, depth - 1), _fol_concept(rng, depth - 1))
    if k < 0.26:
        return dl.Or(_fol_concept(rng, depth - 1), _fol_concept(rng, depth - 1))
    if k < 0.34:
        return dl.Not(_fol_concept(rng, depth - 1))
    if k < 0.58:
        return dl.Exists(rng.choice(("r", "s")), _fol_concept(rng, depth - 1))
    if k < 0.72:
        return dl.ForAll(rng.choice(("r", "s")), _fol_concept(rng, depth - 1))
    if k < 0.84:
        return dl.AtLeast(rng.choice((1, 2)), rng.choice(("r", "s")), _fol_concept(rng, depth - 1))
    return dl.AtMost(rng.choice((0, 1, 2)), rng.choice(("r", "s")), _fol_concept(rng, depth - 1))


def _fol_knowledge_base(rng):
    roles = ("r", "s")
    tbox, abox = dl.TBox(), dl.ABox()
    for _ in range(rng.choice((0, 0, 1, 2))):
        tbox.add(_fol_concept(rng, 1), _fol_concept(rng, 2))
    if rng.random() < 0.35:
        tbox.add_functional_role(rng.choice(roles))
    if rng.random() < 0.2:
        tbox.add_role_inclusion("r", "s")
    if rng.random() < 0.15:
        tbox.add_irreflexive_role(rng.choice(roles))
    if rng.random() < 0.15:
        tbox.add_role_domain(rng.choice(roles), _fol_concept(rng, 1))
    if rng.random() < 0.15:
        tbox.add_role_range(rng.choice(roles), _fol_concept(rng, 1))
    names = rng.sample(FOL_NAMES, rng.choice((2, 3, 3, 4)))
    for _ in range(rng.choice((2, 3, 4))):
        abox.assert_concept(rng.choice(names), _fol_concept(rng, 2))
    for _ in range(rng.choice((0, 1, 2, 3))):
        abox.assert_role(rng.choice(names), rng.choice(names), rng.choice(roles))
    if rng.random() < 0.25 and len(names) > 1:
        abox.assert_same(*rng.sample(names, 2))
    if rng.random() < 0.25 and len(names) > 1:
        abox.assert_distinct(*rng.sample(names, 2))
    if rng.random() < 0.2:
        abox.assert_negative_role(rng.choice(names), rng.choice(names), rng.choice(roles))
    return tbox, abox


def _fol_consistent(tbox, abox):
    kb = dl.kb_to_fol(tbox, abox)
    status = api.prove(FNot(kb.formula), list(kb.axioms), backends=["z3"], timeout=TIMEOUT_MS).status
    return {"refuted": True, "proved": False}.get(status)


def _fol_entails(tbox, abox, individual, query):
    kb = dl.kb_to_fol(tbox, abox, query=[query])
    status = api.prove(kb.instance_goal(individual, query), list(kb.premises),
                       backends=["z3"], timeout=TIMEOUT_MS).status
    return {"proved": True, "refuted": False}.get(status)


#: Seeds of a larger sweep (the first 19: an individual named like a witness changed a
#: verdict of the tableau, which the FOL image does not share) and a few that agreed.
DIFFERENTIAL_SEEDS = (1, 2, 24, 52, 140, 141, 150, 243, 256, 281, 289, 294, 301, 312, 343,
                      379, 470, 516, 582, 3, 4, 5, 6, 7, 8, 9, 10)


@pytest.mark.parametrize("seed", DIFFERENTIAL_SEEDS)
def test_the_tableau_and_the_fol_image_agree_with_individuals_named_like_witnesses(seed, monkeypatch):
    monkeypatch.setattr(tableau, "MAX_STEPS", 20000)
    rng = random.Random(seed * 7919 + 3)
    tbox, abox = _fol_knowledge_base(rng)
    query = _fol_concept(rng, 2)
    individual = rng.choice(sorted(tableau._abox_individual_names(abox)) or ["a"])
    decided = 0
    for question in ("consistent", "entailed"):
        if question == "consistent":
            tableau_says = _verdict(dl.abox_consistent, abox, tbox)
            fol_says = _fol_consistent(tbox, abox) if tableau_says is not None else None
        else:
            tableau_says = _verdict(dl.instance_check, abox, individual, query, tbox)
            fol_says = (_fol_entails(tbox, abox, individual, query)
                        if tableau_says is not None else None)
        if tableau_says is None or fol_says is None:
            continue           # the step budget or Z3's budget ran out: no verdict to compare
        decided += 1
        assert tableau_says is fol_says, (seed, question, repr(abox), repr(tbox))
    # (a seed whose both questions run out of budget proves nothing, and is not expected)
    assert decided >= 1
