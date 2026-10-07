"""Tests for the external OWL 2 DL reasoner backend (unicode_logic_kit.dl.owl_reasoner).

Two tiers:

* Non-live: :func:`available`'s pure-discovery contract, and the translator's
  internal helpers — run unconditionally, no owlready2/Java needed.
* Live (``@pytest.mark.owl_live``, auto-skipped unless owlready2 AND a JVM are
  both present — same convention as ``isabelle_live``/``hets_live``, see
  ``pyproject.toml``'s ``[tool.pytest.ini_options] markers``): the actual
  differential oracle. Every fixture is decided through BOTH
  ``dl.tableau.*`` (or, for I/O, hand-checked expectations with no in-house
  route to compare against) and this module's ``external_*`` twin, and must
  agree exactly:

  - ALCHQ fragment (satisfiability, subsumption, RBox role hierarchy +
    transitivity, qualified number restrictions): differential against
    ``dl.tableau``, reusing a curated subset of ``tests/test_dl_alc.py``'s
    own hand-checked fixtures rather than every existing ALCHQ test file
    verbatim, to keep the live run's JVM-subprocess count bounded (each
    ``external_*`` call spawns a fresh ``java`` subprocess — see
    ``dl.owl_reasoner``'s module docstring).
  - I/O (inverse roles, nominals): hand-checked textbook cases with NO
    in-house second route (the tableau refuses these outright — that is the
    whole point of this module existing), matching the roadmap's own
    corrected test-oracle examples.
"""

import shutil

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit.dl.owl_reasoner import available

owl_live = pytest.mark.owl_live
_JAVA_ON_PATH = shutil.which("java") is not None


def _owl_live_available() -> bool:
    """True iff BOTH owlready2 is importable AND a ``java`` binary is on PATH
    (the two prerequisites an actual HermiT invocation needs — see
    ``dl.owl_reasoner``'s module docstring's "Optional dependency" section for
    why ``available()`` itself deliberately checks only the former).
    """
    return available() and _JAVA_ON_PATH


live = pytest.mark.skipif(not _owl_live_available(),
                           reason="owlready2 and/or a JVM (java on PATH) not found")

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")
r = "r"


# --------------------------------------------------------------------------- #
# Non-live: pure discovery, no owlready2/Java needed.
# --------------------------------------------------------------------------- #

def test_available_is_a_bool():
    assert isinstance(available(), bool)


def test_available_matches_find_spec(monkeypatch):
    # Pure-discovery contract (mirrors atp.cvc5_backend.Cvc5Backend.available):
    # available() must track importlib.util.find_spec("owlready2") exactly,
    # with no import performed to answer it.
    import importlib.util
    import unicode_logic_kit.dl.owl_reasoner as owl_reasoner_module

    real_find_spec = importlib.util.find_spec

    def fake_find_spec(name, *a, **kw):
        if name == "owlready2":
            return None
        return real_find_spec(name, *a, **kw)

    monkeypatch.setattr(owl_reasoner_module.importlib.util, "find_spec", fake_find_spec)
    assert owl_reasoner_module.available() is False


def test_unavailable_raises_owl_reasoner_error(monkeypatch):
    import unicode_logic_kit.dl.owl_reasoner as owl_reasoner_module

    monkeypatch.setattr(owl_reasoner_module, "available", lambda: False)
    with pytest.raises(owl_reasoner_module.OwlReasonerError, match="owlready2"):
        owl_reasoner_module.external_concept_satisfiable(A)


def test_all_individuals_helper():
    # _all_individuals is the SWEEP's scan, the same one the tableau's
    # instance_retrieval/realize_all and kb_to_fol(...).individuals read
    # (dl.tableau._abox_individual_names, driven by the axiom-kind table): a
    # role-only individual still counts, and an ABox that names nobody has NO
    # individual. Hand-derived: the sweep reports the individuals the knowledge
    # base NAMES, and an empty ABox names none, so there is nobody to retrieve or
    # realize -- the answer is the empty set. (The anonymous "a" that
    # dl.tableau._individuals falls back to is a convention of abox_consistent
    # alone: the node a TBox has to run on. Reporting it from a sweep answered
    # about an individual nobody named; the FOL image, which invents none, is
    # checked below. This test pinned {"a"} until the sweeps stopped inventing it.)
    from unicode_logic_kit.dl.owl_reasoner import _all_individuals

    ab = dl.ABox().assert_role("alice", "bob", "hasChild")
    assert _all_individuals(ab) == {"alice", "bob"}
    assert _all_individuals(dl.ABox()) == set()
    assert dl.kb_to_fol(None, dl.ABox()).individuals == ()


def test_a_fresh_individual_is_the_base_or_the_first_numbered_name_outside_the_taken_ones():
    from unicode_logic_kit.dl.owl_reasoner import _fresh_individual

    assert _fresh_individual("_probe", set()) == "_probe"
    assert _fresh_individual("_probe", {"a", "b"}) == "_probe"
    assert _fresh_individual("_probe", {"_probe"}) == "_probe1"
    assert _fresh_individual("_probe", {"_probe", "_probe1", "_probe3"}) == "_probe2"
    # names are compared exactly: a name that differs in case is another name
    assert _fresh_individual("_probe", {"_Probe"}) == "_probe"


@pytest.mark.parametrize("where", ["nominal in the concept", "nominal in a GCI",
                                   "value restriction in a domain axiom", "both numbered names taken"])
def test_the_probe_individual_of_a_satisfiability_question_is_not_an_individual_of_the_question(
        where, monkeypatch):
    # The question "is C satisfiable?" is asked as "is {probe : C} consistent?", and the probe
    # is ONE element. A probe called like an individual that a nominal or a value restriction
    # of the question names would BE that individual (one element, not "some element"):
    # `{p} ⊑ A` with C = ¬A is then inconsistent, although ¬A is satisfiable (the nominal's
    # element in A, another one outside it).
    import unicode_logic_kit.dl.owl_reasoner as module

    taken = {"_probe"}
    concept, tbox = dl.Not(A), dl.TBox()
    if where == "nominal in the concept":
        concept = dl.And(dl.Not(A), dl.Not(dl.Nominal("_probe")))
    elif where == "nominal in a GCI":
        tbox.add(dl.Nominal("_probe"), A)
    elif where == "value restriction in a domain axiom":
        tbox.add_role_domain("r", dl.HasValue("r", "_probe"))
    else:
        tbox.add(dl.Nominal("_probe"), A).add(dl.Nominal("_probe1"), A)
        taken = {"_probe", "_probe1"}
    seen = []
    monkeypatch.setattr(module, "_require_available", lambda: object())
    monkeypatch.setattr(module, "_kb_consistent", lambda tbox_, abox_: seen.append(abox_) or True)
    assert module.external_concept_satisfiable(concept, tbox) is True
    ((probe, asserted),) = seen[0].concept_assertions
    assert probe not in taken and asserted == concept
    assert probe == ("_probe2" if where == "both numbered names taken" else "_probe1")


# --------------------------------------------------------------------------- #
# Live: ALCHQ differential against dl.tableau.
# --------------------------------------------------------------------------- #

@owl_live
@live
@pytest.mark.parametrize("concept, sat", [
    (A, True),
    (dl.And(A, dl.Not(A)), False),
    (dl.Bottom(), False),
    (dl.Top(), True),
    (dl.And(dl.Exists(r, A), dl.ForAll(r, dl.Not(A))), False),
    (dl.And(dl.Exists(r, A), dl.Exists(r, dl.Not(A))), True),
])
def test_differential_concept_satisfiable(concept, sat):
    assert dl.concept_satisfiable(concept) is sat
    assert dl.external_concept_satisfiable(concept) is sat


@owl_live
@live
@pytest.mark.parametrize("sub, sup, holds", [
    (dl.And(A, B), A, True),
    (A, dl.Or(A, B), True),
    (A, B, False),
    (dl.Exists(r, A), dl.Exists(r, dl.Top()), True),
    (dl.And(dl.ForAll(r, A), dl.Exists(r, dl.Top())), dl.Exists(r, A), True),
    (dl.Exists(r, A), dl.ForAll(r, A), False),
])
def test_differential_subsumption(sub, sup, holds):
    assert dl.subsumes(sub, sup) is holds
    assert dl.external_subsumes(sub, sup) is holds


@owl_live
@live
def test_differential_tbox_and_abox():
    t = dl.TBox().add(A, B).add(B, C)
    assert dl.subsumes(A, C, t) is True
    assert dl.external_subsumes(A, C, t) is True

    ab = dl.ABox().assert_concept("alice", A).assert_concept("alice", dl.Not(A))
    assert dl.abox_consistent(ab) is False
    assert dl.external_abox_consistent(ab) is False

    ab2 = (dl.ABox().assert_concept("alice", dl.ForAll(r, A))
           .assert_role("alice", "bob", r).assert_concept("bob", dl.Not(A)))
    assert dl.abox_consistent(ab2) is False
    assert dl.external_abox_consistent(ab2) is False


@owl_live
@live
def test_differential_rbox_hierarchy_and_transitivity():
    # hasChild ⊑ hasDescendant, Trans(hasDescendant):
    # ∃hasChild.∃hasChild.C ⊑ ∃hasDescendant.C — entailed purely by the RBox
    # (dl.tableau's own module-docstring example, see "Role hierarchies and
    # transitive roles (RBox)").
    t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant").add_transitive_role("hasDescendant")
    sub = dl.Exists("hasChild", dl.Exists("hasChild", C))
    sup = dl.Exists("hasDescendant", C)
    assert dl.subsumes(sub, sup, t) is True
    assert dl.external_subsumes(sub, sup, t) is True
    # Negative control: without the RBox axioms, the same subsumption fails.
    assert dl.subsumes(sub, sup) is False
    assert dl.external_subsumes(sub, sup) is False


@owl_live
@live
def test_differential_qualified_number_restrictions():
    # ≥2 r.⊤ ⊓ ≤1 r.⊤ is unsatisfiable (Hollunder & Baader's textbook ALCQ
    # clash: at least 2 pairwise-distinct r-successors but at most 1 — see
    # dl.tableau's module docstring, "Qualified number restrictions").
    clash = dl.And(dl.AtLeast(2, r, dl.Top()), dl.AtMost(1, r, dl.Top()))
    assert dl.concept_satisfiable(clash) is False
    assert dl.external_concept_satisfiable(clash) is False
    # ABox-level: rex has 2 DISTINCT r-successors in C, but is asserted ≤1 r.C.
    ab = (dl.ABox().assert_concept("x", dl.AtMost(1, r, C))
          .assert_concept("y1", C).assert_concept("y2", C)
          .assert_role("x", "y1", r).assert_role("x", "y2", r)
          .assert_distinct("y1", "y2"))
    assert dl.abox_consistent(ab) is False
    assert dl.external_abox_consistent(ab) is False
    # Same ABox WITHOUT the distinctness assertion: y1/y2 may denote the same
    # domain element (no unique name assumption), so it is consistent.
    ab2 = (dl.ABox().assert_concept("x", dl.AtMost(1, r, C))
           .assert_concept("y1", C).assert_concept("y2", C)
           .assert_role("x", "y1", r).assert_role("x", "y2", r))
    assert dl.abox_consistent(ab2) is True
    assert dl.external_abox_consistent(ab2) is True


@owl_live
@live
def test_differential_instance_check_and_retrieval():
    Human, Mortal = dl.Atomic("Human"), dl.Atomic("Mortal")
    t = dl.TBox().add(Human, Mortal)
    ab = dl.ABox().assert_concept("socrates", Human)
    assert dl.instance_check(ab, "socrates", Mortal, t) is True
    assert dl.external_instance_check(ab, "socrates", Mortal, t) is True
    assert dl.instance_retrieval(ab, Mortal, t) == {"socrates"}
    assert dl.external_instance_retrieval(ab, Mortal, t) == {"socrates"}


@owl_live
@live
def test_differential_realize():
    Dog, Mammal, Animal = dl.Atomic("Dog"), dl.Atomic("Mammal"), dl.Atomic("Animal")
    t = dl.TBox().add(Dog, Mammal).add(Mammal, Animal)
    ab = dl.ABox().assert_concept("rex", Dog)
    vocabulary = [Animal, Mammal, Dog, dl.Top()]
    assert dl.realize(ab, "rex", vocabulary, t) == [Dog]
    assert dl.external_realize(ab, "rex", vocabulary, t) == [Dog]
    assert dl.realize_all(ab, vocabulary, t) == dl.external_realize_all(ab, vocabulary, t)


# --------------------------------------------------------------------------- #
# Live: I/O textbook cases — NO in-house second route (dl.tableau refuses
# both outright; this is exactly the fragment this module exists to decide).
# --------------------------------------------------------------------------- #

@owl_live
@live
def test_nominal_no_unique_name_assumption():
    # {a} ⊓ {b}: satisfiable absent an explicit distinctness assertion — OWL
    # 2 has no unique name assumption (Baader et al., DL Handbook; also
    # confirmed independently via the Z3-backed FOL translation in
    # tests/test_dl_alc.py's test_translate_nominal_no_unique_name_assumption_both_directions).
    concept = dl.And(dl.Nominal("a"), dl.Nominal("b"))
    assert dl.external_concept_satisfiable(concept) is True


@owl_live
@live
def test_nominal_with_distinctness_is_unsatisfiable():
    # Same {a} ⊓ {b}, but now asserted via an ABox with a and b forced
    # distinct: no model can put the SAME probe individual into both
    # singletons, so this is unsatisfiable.
    ab = (dl.ABox().assert_concept("_probe", dl.And(dl.Nominal("a"), dl.Nominal("b")))
          .assert_distinct("a", "b"))
    assert dl.external_abox_consistent(ab) is False


@owl_live
@live
@pytest.mark.parametrize("individual", ["p", "_probe", "_probe1"])
def test_a_nominal_named_like_the_probe_does_not_make_a_satisfiable_concept_unsatisfiable(individual):
    # {i} ⊑ A and the concept ¬A. Satisfiable, whatever the individual i is called:
    # the structure {0, 1} with i ↦ 0, A = {0} puts the element 1 in ¬A (the nominal's own
    # element is in A, and a concept asks for SOME element). For the same reason A does not
    # subsume ⊤ here: the element 1 is no A.
    tbox = dl.TBox().add(dl.Nominal(individual), A)
    assert dl.external_concept_satisfiable(dl.Not(A), tbox) is True
    assert dl.external_subsumes(dl.Top(), A, tbox) is False
    # and the FOL image agrees: ¬A is not refuted from the terminology
    from unicode_logic_kit import api
    kb = dl.kb_to_fol(tbox, None, query=[dl.Not(A)])
    status = api.prove(kb.unsatisfiability_goal(dl.Not(A)), list(kb.tbox_premises),
                       backends=["z3"], timeout=20000).status
    assert status == "refuted"


@owl_live
@live
def test_inverse_role_entailment_corrected_textbook_case():
    # Corrected test-oracle example (concept-level InverseRole wrapper, not a
    # named-inverse-role RBox declaration, which this kit's AST does not
    # have): (a, b):hasChild entails b : ∃hasChild⁻.⊤ (b has an INCOMING
    # hasChild edge, i.e. an hasChild-inverse successor, namely a).
    ab = dl.ABox().assert_role("a", "b", "hasChild")
    query = dl.Exists(dl.InverseRole("hasChild"), dl.Top())
    assert dl.external_instance_check(ab, "b", query) is True


@owl_live
@live
def test_inverse_role_not_entailed_countermodel():
    # Negative control: only (a, c):hasChild — b has NO incoming hasChild
    # edge, so the same query is NOT entailed for b.
    ab = dl.ABox().assert_role("a", "c", "hasChild")
    query = dl.Exists(dl.InverseRole("hasChild"), dl.Top())
    assert dl.external_instance_check(ab, "b", query) is False


@owl_live
@live
def test_inverse_role_with_role_hierarchy_and_number_restriction():
    # Combines I with H/Q, still decided correctly: hasSon ⊑ hasChild, and
    # (a,b):hasSon — b's inverse-hasChild successor set (via the hierarchy)
    # includes a, so ∃hasChild⁻.⊤ is entailed for b even though only a
    # hasSon edge (never a literal hasChild edge) was ever asserted.
    t = dl.TBox().add_role_inclusion("hasSon", "hasChild")
    ab = dl.ABox().assert_role("a", "b", "hasSon")
    query = dl.Exists(dl.InverseRole("hasChild"), dl.Top())
    assert dl.external_instance_check(ab, "b", query, t) is True


# =============================================================================
# B1b: every role-box field reaches the ontology this module builds. The whole
# point of this module is to be an INDEPENDENT oracle, and it is the route the
# in-house tableau's own refusal messages send the user to -- an oracle that
# silently drops the axiom under test agrees with everything, and those
# messages would be dishonest. Measured before 0.30.0: `_build_kb` read only
# `role_inclusions` and `transitive_roles`, so all nine new fields were lost,
# and an InverseRole in an inclusion came out as a BRAND-NEW atomic property.
#
# Each case is chosen so the verdict FLIPS when the field is dropped, which is
# what makes it a test of the wiring rather than of HermiT.
# =============================================================================

def _flips(expected, with_box, without_box=None):
    """``(expected, tbox)`` pairs: the axiom present, and absent."""
    return [(expected, with_box), (not expected, without_box or dl.TBox())]


@owl_live
@live
def test_external_route_carries_an_inverse_property_pair():
    # PartOf(alice, bob) and PartOf ≡ HasPart⁻ give HasPart(bob, alice).
    ab = dl.ABox().assert_role("alice", "bob", "partOf")
    query = dl.Exists("hasPart", dl.Top())
    for expected, t in _flips(True, dl.TBox().add_inverse_roles("partOf", "hasPart")):
        assert dl.external_instance_check(ab, "bob", query, t) is expected


@owl_live
@live
def test_external_route_carries_a_property_chain():
    # alice -p-> bob -q-> carol is the chain's antecedent, so (alice, carol)
    # is a t-pair.
    ab = dl.ABox().assert_role("alice", "bob", "p").assert_role("bob", "carol", "q")
    query = dl.Exists("t", dl.Top())
    for expected, t in _flips(True, dl.TBox().add_role_chain(("p", "q"), "t")):
        assert dl.external_instance_check(ab, "alice", query, t) is expected


@owl_live
@live
def test_external_route_carries_role_disjointness():
    # p ⊑ q makes every p-pair a q-pair, so a p-pair would be in both; with
    # Disj(p, q) that is impossible, hence p is empty and ∃p.⊤ unsatisfiable.
    full = dl.TBox().add_role_inclusion("p", "q").add_disjoint_roles("p", "q")
    hierarchy_only = dl.TBox().add_role_inclusion("p", "q")
    for expected, t in _flips(False, full, hierarchy_only):
        assert dl.external_concept_satisfiable(dl.Exists("p", dl.Top()), t) is expected


@owl_live
@live
def test_external_route_carries_a_symmetric_role():
    ab = dl.ABox().assert_role("alice", "bob", "p")
    query = dl.Exists("p", dl.Top())
    for expected, t in _flips(True, dl.TBox().add_symmetric_role("p")):
        assert dl.external_instance_check(ab, "bob", query, t) is expected


@owl_live
@live
def test_external_route_carries_a_reflexive_role():
    # Every individual is its own p-neighbour, so ∀p.A forces A onto it.
    for expected, t in _flips(True, dl.TBox().add_reflexive_role("p")):
        assert dl.external_subsumes(dl.ForAll("p", A), A, t) is expected


@owl_live
@live
def test_external_route_carries_an_asymmetric_role():
    ab = dl.ABox().assert_role("alice", "bob", "p").assert_role("bob", "alice", "p")
    for expected, t in _flips(False, dl.TBox().add_asymmetric_role("p")):
        assert dl.external_abox_consistent(ab, t) is expected


@owl_live
@live
def test_external_route_carries_an_irreflexive_role():
    ab = dl.ABox().assert_role("alice", "alice", "p")
    for expected, t in _flips(False, dl.TBox().add_irreflexive_role("p")):
        assert dl.external_abox_consistent(ab, t) is expected


@owl_live
@live
def test_external_route_carries_a_functional_role():
    sub = dl.And(dl.Exists("p", A), dl.Exists("p", B))
    sup = dl.Exists("p", dl.And(A, B))
    for expected, t in _flips(True, dl.TBox().add_functional_role("p")):
        assert dl.external_subsumes(sub, sup, t) is expected


@owl_live
@live
def test_external_route_carries_an_inverse_functional_role():
    # alice and bob are both p-predecessors of carol, so ≤1 p⁻.⊤ identifies
    # them -- and they are forced distinct.
    ab = (dl.ABox().assert_role("alice", "carol", "p")
          .assert_role("bob", "carol", "p").assert_distinct("alice", "bob"))
    for expected, t in _flips(False, dl.TBox().add_inverse_functional_role("p")):
        assert dl.external_abox_consistent(ab, t) is expected


@owl_live
@live
def test_external_route_carries_an_inverse_role_in_a_role_inclusion():
    # r ⊑ s⁻ makes r(alice, bob) witness s(bob, alice). Measured before 0.30.0:
    # this returned False, SILENTLY -- `_build_kb` used the InverseRole as a
    # dict key, so the axiom became `r ⊑ <a fresh atomic property>`.
    ab = dl.ABox().assert_role("alice", "bob", "r")
    query = dl.Exists("s", dl.Top())
    t = dl.TBox().add_role_inclusion("r", dl.InverseRole("s"))
    assert dl.external_instance_check(ab, "bob", query, t) is True
    assert dl.external_instance_check(ab, "bob", query, dl.TBox()) is False


def test_external_route_refuses_a_non_simple_role_box_with_the_kits_own_error():
    # Not a live test: the check runs BEFORE owlready2 is touched, so the
    # kit's own NonSimpleRoleError is what the user sees on every route rather
    # than a HermiT error on one and a tableau error on another.
    t = dl.TBox().add_transitive_role("r").add_asymmetric_role("r")
    with pytest.raises(dl.NonSimpleRoleError, match="AsymmetricObjectProperty"):
        dl.external_concept_satisfiable(A, t)
    with pytest.raises(dl.NonSimpleRoleError, match="'r'"):
        dl.external_abox_consistent(dl.ABox(), t)


def _data_layer_sample(holder_name, field):
    """A knowledge base ``(tbox, abox)`` whose ONLY content is one valid entry of
    the data-layer ``field``, its shape read off the dataclass annotation
    (``List[Tuple[str, DataRange]]``, ``Set[str]``, ...) so that a field added to
    the table needs no sample written by hand — and one with an annotation this
    helper has no value for fails here with the instruction to add one."""
    import typing

    from unicode_logic_kit.dl.datatypes import DataRange, Datatype, Literal

    holder_cls = dl.TBox if holder_name == "tbox" else dl.ABox
    hint = typing.get_type_hints(holder_cls)[field]
    container_type, (element_type,) = typing.get_origin(hint), typing.get_args(hint)
    names = iter("pqrstuvw")

    def sample(tp):
        if typing.get_origin(tp) is tuple:
            return tuple(sample(arg) for arg in typing.get_args(tp))
        if tp is str:
            return next(names)
        if tp is dl.Concept:
            return dl.Atomic("A")
        if tp is DataRange:
            return Datatype("xsd:integer")
        if tp is Literal:
            return Literal("1", "xsd:integer")
        raise AssertionError(
            f"{holder_cls.__name__}.{field}: no sample value for the annotation "
            f"{tp!r}: add one to _data_layer_sample so the data-layer refusal "
            "stays derived from the table")

    holder = holder_cls()
    entry = sample(element_type)
    stored = getattr(holder, field)
    assert isinstance(stored, container_type)
    if container_type is list:
        stored.append(entry)
    else:
        stored.add(entry)
    return (holder, dl.ABox()) if holder_name == "tbox" else (dl.TBox(), holder)


def test_characteristics_table_covers_every_characteristic_field():
    # The bases tuple owlready2 needs is built from a table; a field missing
    # from it would be dropped SILENTLY, since owlready2 cannot add a
    # characteristic after the property class is created.
    #
    # Two halves, both derived from the axiom-kind table's LAYER column rather
    # than from a list of names, so that a future TBox field cannot slip
    # between them: an OBJECT-layer side field is rendered here (a
    # characteristic, or one of the six handled explicitly in _build_kb), and
    # every DATA-layer field makes this route refuse by name.
    from unicode_logic_kit.dl import owl_reasoner as _r
    from unicode_logic_kit.dl.tableau import _AXIOM_KINDS, _holder_fields

    side = set(_holder_fields("tbox", part="side"))
    object_side = set(_holder_fields("tbox", part="side", layer="object"))
    data_side = set(_holder_fields("tbox", part="side", layer="data"))
    assert side == object_side | data_side and not object_side & data_side
    characteristic_fields = set(_r._CHARACTERISTIC_BASES)
    assert characteristic_fields <= object_side
    # the OBJECT fields that are NOT one-role characteristics are handled
    # explicitly in _build_kb instead
    assert object_side - characteristic_fields == {
        "role_inclusions", "disjoint_role_pairs", "inverse_role_pairs",
        "role_chains", "role_domains", "role_ranges"}
    # the DATA fields are not rendered at all, and none of them is a
    # characteristic: this route has no data domain
    assert data_side and not data_side & characteristic_fields

    # The second half of the statement above (the same test: it needs the
    # same table, and starts no JVM either). dl.owl_reasoner does not render the
    # data layer, and an oracle that dropped a data axiom silently would agree
    # with everything -- so a knowledge base carrying ANY data-layer field is
    # refused by name, from every entry point, before any reasoner is started.
    # The fields are read off _AXIOM_KINDS' layer column, TBox and ABox alike;
    # an empty vocabulary reaches no HermiT call, so this starts no JVM.
    checked = []
    for holder_name in ("tbox", "abox"):
        for field in _holder_fields(holder_name, layer="data"):
            tbox, abox = _data_layer_sample(holder_name, field)
            kinds = [row.kind for row in _AXIOM_KINDS
                     if row.holder == holder_name and row.field == field]
            assert kinds, field
            with pytest.raises(dl.UnsupportedAxiomError, match="data-layer") as info:
                dl.external_realize(abox, "a", [], tbox)
            for kind in kinds:
                assert kind in str(info.value), (field, kind, str(info.value))
            with pytest.raises(dl.UnsupportedAxiomError, match="data-layer"):
                dl.external_realize_all(abox, [], tbox)
            with pytest.raises(dl.UnsupportedAxiomError, match="data-layer"):
                dl.external_instance_retrieval(abox, A, tbox)
            checked.append(field)
    # not vacuous, and every data-layer field of BOTH holders was visited
    assert checked and len(checked) == len(set(checked))
    assert set(checked) == (set(_holder_fields("tbox", layer="data"))
                            | set(_holder_fields("abox", layer="data")))
