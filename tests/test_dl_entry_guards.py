r"""Every public entry point runs the guard, and the individuals are the ABox's.

Three things that were true of the reduction chain and false of its edges:

**No entry point returns before the guard has run.** The in-house tableau has two
functions that decide anything, ``concept_satisfiable`` and ``abox_consistent``,
and everything else reduces to them — "inherits the guard" — which is a guard only
WHEN THERE IS SOMETHING TO REDUCE. ``realize`` with an empty vocabulary,
``realize_all`` and ``instance_retrieval`` on an empty ABox, and ``classify`` with
fewer than two names make no call to either, so a knowledge base carrying a refused
axiom kind got a quiet ``[]``/``{}``/an empty hierarchy where every other entry
point raised. The audit of the package's public entry points, with the result:

======================================  =====================================
entry point                             how the guard is reached
======================================  =====================================
``concept_satisfiable``                 first statement (``_reject_role_box``)
``concept_unsatisfiable``/``subsumes``/  reduce to ``concept_satisfiable``
``equivalent``
``abox_consistent``                     first statement
``instance_check``                      reduces to ``abox_consistent``
``instance_retrieval``                  ``_reject_inputs`` (was: nothing, on an
                                        empty ABox)
``realize``/``realize_all``             ``_reject_inputs`` (was: nothing, on an
                                        empty vocabulary or ABox)
``classify``                            ``_reject_role_box`` + ``_reject_inputs``
                                        (was: the kind guard only)
``external_*`` (HermiT)                 ``_guard_inputs`` in ``_kb_consistent``
                                        and at the top of ``external_realize``/
                                        ``external_realize_all``/
                                        ``external_instance_retrieval`` (was:
                                        nothing, for an empty vocabulary/ABox)
``kb_to_fol`` and the other images      value validation in
                                        ``_collect_vocabulary`` / ``_rbox_axioms``
======================================  =====================================

**An ABox that names nobody has no individuals.** ``abox_consistent`` seeds an
anonymous node ``a`` so an empty ABox still has an element for the TBox to run on
(the domain is non-empty); the SWEEPS ``instance_retrieval`` and ``realize_all``
read that node as if somebody had named it, and reported ``{"a"}`` for
``TBox().add(Top(), A)``, while ``kb_to_fol(...).individuals`` is ``()`` and the
FOL route never invented it. This predates the OWL work: an original ALC test
pinned ``realize_all(empty, [A, Top()]) == {"a": [Top()]}``.

**The oracle must not reason over a weaker knowledge base.** ``dl.owl_reasoner``
applied ``ObjectPropertyDomain``/``Range`` and property chains by ASSIGNMENT, so a
second axiom on one role replaced the first. HermiT is never started here: the
built owlready2 objects are inspected directly.

Every expected value is hand-derived in the comment above it.
"""

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl import owl_reasoner as _owl
from unicode_logic_kit.dl.tableau import _abox_individual_names
from unicode_logic_kit.fol.nodes import Not as FNot

A, B = dl.Atomic("A"), dl.Atomic("B")
TIMEOUT_MS = 30000


# --------------------------------------------------------------------------- #
# The refused knowledge bases: every kind the in-house tableau has no rule for.
# --------------------------------------------------------------------------- #

_REFUSED = [
    ("symmetric", lambda: dl.TBox().add_symmetric_role("r")),
    ("reflexive", lambda: dl.TBox().add_reflexive_role("r")),
    ("inverse functional", lambda: dl.TBox().add_inverse_functional_role("r")),
    ("inverse pair", lambda: dl.TBox().add_inverse_roles("p", "q")),
    ("chain", lambda: dl.TBox().add_role_chain(["a", "b"], "c")),
    ("inverse inclusion, super", lambda: dl.TBox().add_role_inclusion("r", dl.InverseRole("s"))),
    ("inverse inclusion, sub", lambda: dl.TBox().add_role_inclusion(dl.InverseRole("s"), "r")),
    # the data layer: refused by the tableau for a different reason, same guard
    ("data property", lambda: dl.TBox().add_functional_data_property("d")),
    ("data range", lambda: dl.TBox().add_data_property_range("d", "xsd:integer")),
]

# Each call reaches NO instance_check / subsumes at all: nothing to realize, an
# empty vocabulary, or fewer than two names.
_EMPTY_CALLS = [
    ("realize, empty vocabulary", lambda t: dl.realize(dl.ABox(), "a", [], t)),
    ("realize, empty vocabulary, named ABox",
     lambda t: dl.realize(dl.ABox().assert_concept("a", A), "a", [], t)),
    ("realize_all, empty everything", lambda t: dl.realize_all(dl.ABox(), [], t)),
    ("realize_all, empty vocabulary",
     lambda t: dl.realize_all(dl.ABox().assert_concept("a", A), [], t)),
    ("realize_all, empty ABox", lambda t: dl.realize_all(dl.ABox(), [A], t)),
    ("instance_retrieval, empty ABox", lambda t: dl.instance_retrieval(dl.ABox(), A, t)),
    ("classify, no names", lambda t: dl.classify(t)),
    ("classify, one name", lambda t: dl.classify(t, [A])),
]


@pytest.mark.parametrize("label, call", _EMPTY_CALLS, ids=[c[0] for c in _EMPTY_CALLS])
@pytest.mark.parametrize("kind, build", _REFUSED, ids=[c[0] for c in _REFUSED])
def test_an_entry_point_with_nothing_to_reduce_still_refuses_a_refused_kind(
        kind, build, label, call):
    # Each of these kinds is outside ALCHQ BY ROW of the axiom-kind table, so
    # every entry point refuses it whatever the question — including a question
    # with no individual and no concept in it.
    with pytest.raises(dl.UnsupportedAxiomError):
        call(build())


def test_a_refused_assertion_kind_is_refused_by_the_empty_sweeps_too():
    # The ABox half: a data assertion is a refused kind, and an empty
    # vocabulary must not hide it.
    abox = dl.ABox().assert_data("a", "d", dl.Literal("1", "xsd:integer"))
    with pytest.raises(dl.UnsupportedAxiomError):
        dl.realize_all(abox, [], dl.TBox())
    with pytest.raises(dl.UnsupportedAxiomError):
        dl.realize(abox, "a", [], dl.TBox())


@pytest.mark.parametrize("label, call", [
    # a nominal anywhere a class expression is stored or asked
    ("realize_all, nominal in the vocabulary, empty ABox",
     lambda: dl.realize_all(dl.ABox(), [dl.Nominal("a")])),
    ("instance_retrieval, nominal query, empty ABox",
     lambda: dl.instance_retrieval(dl.ABox(), dl.Nominal("a"))),
    ("classify, nominal in a domain filler, no names",
     lambda: dl.classify(dl.TBox().add_role_domain("r", dl.Nominal("a")))),
    ("classify, inverse role in a range filler, one name",
     lambda: dl.classify(dl.TBox().add(A, A).add_role_range(
         "r", dl.Exists(dl.InverseRole("s"), dl.Top())))),
])
def test_the_concept_guard_runs_on_the_empty_paths_too(label, call):
    with pytest.raises(dl.UnsupportedConceptError):
        call()


def test_the_data_restriction_guard_runs_on_the_empty_paths_too():
    with pytest.raises(dl.UnsupportedConceptError, match="data restriction"):
        dl.classify(dl.TBox().add(A, A).add_role_range(
            "r", dl.DataHasValue("d", dl.Literal("1", "xsd:integer"))))


@pytest.mark.parametrize("kind, build", _REFUSED, ids=[c[0] for c in _REFUSED])
@pytest.mark.parametrize("label, call", [
    ("external_realize, empty vocabulary",
     lambda t: dl.external_realize(dl.ABox(), "a", [], t)),
    ("external_realize_all, empty vocabulary",
     lambda t: dl.external_realize_all(dl.ABox().assert_concept("a", A), [], t)),
])
def test_the_external_route_refuses_the_data_layer_before_any_reasoner_call(
        label, call, kind, build):
    # HermiT is never reached by these calls (an empty vocabulary reaches none),
    # so this starts no JVM. The external route decides the object kinds the
    # tableau refuses, so only the DATA layer and a non-simple role box are its
    # refusals; for the object kinds it must simply not raise.
    tbox = build()
    if "data" in kind:
        with pytest.raises(dl.UnsupportedAxiomError, match="data-layer"):
            call(tbox)
    else:
        assert call(tbox) in ([], {"a": []})


def test_the_external_route_runs_the_simple_role_check_with_nothing_to_reduce():
    # Trans(r) with Func(r): Functional on a non-simple role, OWL 2 §11. The
    # kit's own error, before any reasoner call, even for an empty vocabulary.
    tbox = dl.TBox().add_transitive_role("r").add_functional_role("r")
    with pytest.raises(dl.NonSimpleRoleError, match="FunctionalObjectProperty"):
        dl.external_realize(dl.ABox(), "a", [], tbox)
    with pytest.raises(dl.NonSimpleRoleError, match="FunctionalObjectProperty"):
        dl.external_realize_all(dl.ABox(), [], tbox)
    with pytest.raises(dl.NonSimpleRoleError, match="FunctionalObjectProperty"):
        dl.external_instance_retrieval(dl.ABox(), A, tbox)


# --------------------------------------------------------------------------- #
# The audit table above, counted from the code and not from memory.
# --------------------------------------------------------------------------- #

def _callers_of(module, name):
    """The names of the functions in ``module`` whose body calls ``name(...)``."""
    import ast
    import inspect

    found = set()
    for function in ast.walk(ast.parse(inspect.getsource(module))):
        if not isinstance(function, ast.FunctionDef):
            continue
        for node in ast.walk(function):
            if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                    and node.func.id == name):
                found.add(function.name)
    return found


def test_the_guard_is_called_from_exactly_the_places_the_documentation_counts():
    # The prose (the module docstring of dl.tableau, the docstrings of the guard
    # functions, the comments of tests/test_dl_rbox.py and
    # tests/test_dl_route_agreement.py) says: ONE axiom-level guard,
    # _reject_unsupported, whose only caller is _reject_role_box; that is the
    # first statement of concept_satisfiable, abox_consistent and classify, and
    # _reject_inputs -- which opens instance_retrieval, realize, realize_all and
    # classify -- calls it too. subsumes, equivalent, concept_unsatisfiable and
    # instance_check hold no guard and inherit it. That prose went stale once
    # (it said "exactly two"), so the counts are pinned here by reading the
    # source: a new entry point with no guard, or a guard call that moves, fails
    # this test instead of leaving the documentation wrong.
    from unicode_logic_kit.dl import classification, tableau

    assert _callers_of(tableau, "_reject_unsupported") == {"_reject_role_box"}
    assert (_callers_of(tableau, "_reject_role_box")
            | _callers_of(classification, "_reject_role_box")) == {
        "concept_satisfiable", "abox_consistent", "classify", "_reject_inputs"}
    assert (_callers_of(tableau, "_reject_inputs")
            | _callers_of(classification, "_reject_inputs")) == {
        "instance_retrieval", "realize", "realize_all", "classify"}
    # and the four that hold no guard of their own really call none of the three
    for name in ("subsumes", "equivalent", "concept_unsatisfiable", "instance_check"):
        for guard in ("_reject_role_box", "_reject_inputs", "_reject_unsupported"):
            assert name not in _callers_of(tableau, guard), (name, guard)


# --------------------------------------------------------------------------- #
# An ABox that names nobody has no individuals.
# --------------------------------------------------------------------------- #

def test_an_empty_abox_retrieves_nobody():
    # TBox: ⊤ ⊑ A, ABox: nothing. Every ELEMENT is an A, but no INDIVIDUAL of
    # the knowledge base is named, so the set of named individuals that are
    # entailed to be A is empty. (It was {"a"}: the anonymous node.)
    tbox = dl.TBox().add(dl.Top(), A)
    assert dl.instance_retrieval(dl.ABox(), A, tbox) == set()
    assert dl.realize_all(dl.ABox(), [A], tbox) == {}
    # The FOL image agrees: it names no individual either.
    assert dl.kb_to_fol(tbox, dl.ABox()).individuals == ()


def test_the_anonymous_node_still_makes_an_empty_abox_a_knowledge_base_with_an_element():
    # What the fallback is FOR, and still does: OWL 2's domain is non-empty, so
    # ⊤ ⊑ ⊥ is INCONSISTENT even over an empty ABox. Hand-derived: Δ ≠ ∅, and
    # every element would have to be in ⊥. The FOL image agrees.
    tbox = dl.TBox().add(dl.Top(), dl.Bottom())
    assert dl.abox_consistent(dl.ABox(), tbox) is False
    kb = dl.kb_to_fol(tbox, dl.ABox())
    assert api.prove(FNot(kb.formula), list(kb.axioms), timeout=TIMEOUT_MS).status == "proved"


@pytest.mark.parametrize("abox", [
    dl.ABox(),
    dl.ABox().assert_negative_role("p", "q", "r"),
    dl.ABox().assert_same("x", "y"),
    dl.ABox().assert_distinct("m", "n"),
    dl.ABox().assert_role("alice", "bob", "hasChild").assert_concept("carol", A),
    dl.ABox().assert_data("d1", "d", dl.Literal("1", "xsd:integer")),
])
def test_the_sweeps_and_the_fol_image_read_the_same_individuals(abox):
    # The two sweeps, the FOL image's `individuals` and the external route's
    # scan are ONE scan (the axiom-kind table's individual_positions column),
    # none of them with a fallback. The data-assertion row is the one the
    # external route's own hand-written scan missed.
    names = sorted(_abox_individual_names(abox))
    assert list(dl.kb_to_fol(None, abox).individuals) == names
    assert sorted(_owl._all_individuals(abox)) == names
    if "d1" not in names:      # the tableau refuses the data layer by name
        assert sorted(dl.realize_all(abox, [], dl.TBox())) == names


# --------------------------------------------------------------------------- #
# The HermiT oracle's knowledge base: appended, never assigned (owlready2
# objects inspected directly; no reasoner is started).
# --------------------------------------------------------------------------- #

owlready2_missing = pytest.mark.skipif(not _owl.available(),
                                       reason="owlready2 is not installed ([owl] extra)")


def _build(tbox, abox=None):
    import owlready2 as ow

    abox = abox if abox is not None else dl.ABox()
    world = ow.World()
    onto = world.get_ontology("http://unicode-logic-kit.invalid/test#")
    ctx = _owl._Ctx(ow, world, onto, _owl._characteristics(tbox))
    with onto:
        _owl._build_kb(ctx, tbox, abox)
    return ctx


@owlready2_missing
def test_two_domain_axioms_on_one_role_are_both_built():
    # ObjectPropertyDomain(r A) and ObjectPropertyDomain(r B): an element with an
    # r-successor is in A AND in B (two domains are a conjunction). Assigning
    # `role.domain = [...]` kept only the last.
    ctx = _build(dl.TBox().add_role_domain("r", A).add_role_domain("r", B))
    assert set(ctx.role_obj("r").domain) == {ctx.cls("A"), ctx.cls("B")}


@owlready2_missing
def test_two_range_axioms_on_one_role_are_both_built():
    ctx = _build(dl.TBox().add_role_range("r", A).add_role_range("r", B))
    assert set(ctx.role_obj("r").range) == {ctx.cls("A"), ctx.cls("B")}


@owlready2_missing
def test_two_chains_with_one_super_role_are_both_built():
    # a1 ∘ a2 ⊑ c and b1 ∘ b2 ⊑ c are two axioms; both must reach the oracle.
    ctx = _build(dl.TBox().add_role_chain(["a1", "a2"], "c")
                 .add_role_chain(["b1", "b2"], "c"))
    chains = ctx.role_obj("c").property_chain
    assert [[p for p in chain.properties] for chain in chains] == [
        [ctx.role_obj("a1"), ctx.role_obj("a2")],
        [ctx.role_obj("b1"), ctx.role_obj("b2")]]


@owlready2_missing
def test_a_second_inverse_pair_is_kept_as_an_equivalence():
    # InverseObjectProperties(p q) and (p r): q = p⁻ = r, so q ≡ r. owlready2's
    # inverse_property holds one property, so the second pair is the equivalence.
    ctx = _build(dl.TBox().add_inverse_roles("p", "q").add_inverse_roles("p", "r"))
    assert ctx.role_obj("p").inverse_property is ctx.role_obj("q")
    assert ctx.role_obj("r") in ctx.role_obj("q").equivalent_to


@owlready2_missing
def test_a_role_inclusion_with_an_inverse_role_on_the_left_is_built():
    # s⁻ ⊑ r says every s(y, x) is an r(x, y), i.e. every s(x, y) is an r(y, x):
    # that is s ⊑ r⁻, which owlready2 can attach to the property s. (Building it
    # as written crashed with an AttributeError; r ⊑ s⁻ always built.)
    ctx = _build(dl.TBox().add_role_inclusion(dl.InverseRole("s"), "r"))
    inverses = [e for e in ctx.role_obj("s").is_a if type(e).__name__ == "Inverse"]
    assert [e.property for e in inverses] == [ctx.role_obj("r")]
    # s⁻ ⊑ r⁻ is s ⊑ r: the inverses cancel.
    ctx = _build(dl.TBox().add_role_inclusion(dl.InverseRole("s"), dl.InverseRole("r")))
    assert ctx.role_obj("r") in ctx.role_obj("s").is_a
