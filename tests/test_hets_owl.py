"""Tests for :mod:`unicode_fol_kit.hets.owl_backend` — the second, independent
external OWL 2 DL reasoner route (Hets/FaCT++), over the ALCHQ + I + O
fragment.

Two tiers, mirroring ``tests/test_owl_reasoner.py``'s split (and, for the
Hets-server gating specifically, ``tests/test_hets_client.py``'s):

Non-live (default run, no server/JVM needed) — the OWL 2 Functional-Style
renderer (:func:`~unicode_fol_kit.hets.owl_backend._render_document` /
``_render_ce``), hand-checked against literal expected text, and
:class:`~unicode_fol_kit.hets.owl_backend.HetsOwlError`/``BackendUnavailable``
propagation with the real network calls monkeypatched away.

Live (``@pytest.mark.hets_live``, gated by ``hets_available()`` exactly like
``test_hets_client.py``'s ``TestHetsLive`` — run explicitly and SERIALLY:
``pytest -m hets_live tests/test_hets_owl.py``) — the actual differential
oracle:

* ALCHQ fragment: every fixture decided through BOTH ``dl.tableau.*`` and
  this module's ``external_*`` twin, and must agree exactly. Reuses a subset
  of ``tests/test_owl_reasoner.py``'s own hand-checked ALCHQ fixtures
  verbatim (same textbook cases, same comments) rather than inventing new
  ones — the whole point is comparing FaCT++-via-Hets against the SAME
  questions HermiT-via-owlready2 already answers correctly there, not a
  differently-shaped battery.
* I/O fragment (inverse roles, nominals — outside ALCHQ, so ``dl.tableau``
  refuses these outright and there is no in-house route to compare against):
  differential against :mod:`unicode_fol_kit.dl.owl_reasoner` instead,
  additionally gated on ``@pytest.mark.owl_live`` (owlready2 + a JVM), since
  that is the SECOND external route these tests need reachable. Same
  hand-checked textbook cases as ``test_owl_reasoner.py``'s I/O section.

See ``unicode_fol_kit/hets/owl_backend.py``'s own module docstring, "Phase 0
spike findings", for the live evidence (exact REST calls/responses) that
justified building this backend at all, and why it always passes
``reasoner="Fact"`` explicitly rather than a Pellet/HermiT identifier neither
this image nor its REST API offers.
"""

import shutil

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.atp.protocol import BackendUnavailable
from unicode_fol_kit.dl.concepts import InverseRole, Nominal
from unicode_fol_kit.hets.docker import hets_available
from unicode_fol_kit.hets.owl_backend import (
    HetsOwlError,
    _kb_consistent, _NameMap, _render_ce, _render_document,
    external_abox_consistent, external_concept_satisfiable,
    external_concept_unsatisfiable, external_equivalent, external_instance_check,
    external_instance_retrieval, external_realize, external_realize_all,
    external_subsumes, hets_owl_available,
)

hets_live = pytest.mark.hets_live
owl_live = pytest.mark.owl_live

_JAVA_ON_PATH = shutil.which("java") is not None


def _owl_live_available() -> bool:
    """Mirrors ``tests/test_owl_reasoner.py``'s own helper exactly: both
    owlready2 AND a JVM must be present for the I/O-vs-``dl.owl_reasoner``
    differential tests to run.
    """
    from unicode_fol_kit.dl.owl_reasoner import available
    return available() and _JAVA_ON_PATH


live_hets = pytest.mark.skipif(
    not hets_available(),
    reason="no reachable HETS server (set $UFK_HETS_URL, or run "
           "`docker run -d --rm -p 8000:8000 spechub2/hets:latest`)")
live_owl = pytest.mark.skipif(
    not _owl_live_available(),
    reason="owlready2 and/or a JVM (java on PATH) not found")

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")
r = "r"


# =============================================================================
# Non-live: the renderer, hand-checked against literal expected text.
# =============================================================================

def test_render_document_empty_tbox_abox():
    text = _render_document(dl.TBox(), dl.ABox())
    assert text == (
        "Prefix(:=<http://unicode-fol-kit.invalid/owl#>)\n"
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
        "Ontology(<http://unicode-fol-kit.invalid/hets-owl-probe>)"
    )


def test_render_document_hand_checked():
    # One inclusion, one concept assertion: names are allocated in the exact
    # order the renderer visits them (RBox, then TBox inclusions, then ABox
    # assertions) -- Doctor is seen first (as the SUBclass of the one
    # inclusion), so it gets :C1; Person (the SUPERclass) gets :C2; alice
    # (the one individual) gets :I1.
    tbox = dl.TBox().add(dl.Atomic("Doctor"), dl.Atomic("Person"))
    abox = dl.ABox().assert_concept("alice", dl.Atomic("Doctor"))
    text = _render_document(tbox, abox)
    assert text == (
        "Prefix(:=<http://unicode-fol-kit.invalid/owl#>)\n"
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
        "Ontology(<http://unicode-fol-kit.invalid/hets-owl-probe>\n"
        "  Declaration(Class(:C1))\n"
        "  Declaration(Class(:C2))\n"
        "  Declaration(NamedIndividual(:I1))\n"
        "  SubClassOf(:C1 :C2)\n"
        "  ClassAssertion(:C1 :I1)\n"
        ")"
    )


def test_render_document_rbox_axioms_precede_tbox_axioms():
    tbox = (dl.TBox().add_role_inclusion("hasSon", "hasChild")
            .add_transitive_role("hasChild")
            .add(dl.Atomic("A"), dl.Atomic("B")))
    text = _render_document(tbox, dl.ABox())
    lines = text.splitlines()
    sub_prop_idx = next(i for i, l in enumerate(lines) if l.strip().startswith("SubObjectPropertyOf"))
    trans_idx = next(i for i, l in enumerate(lines) if l.strip().startswith("TransitiveObjectProperty"))
    subclass_idx = next(i for i, l in enumerate(lines) if l.strip().startswith("SubClassOf"))
    assert sub_prop_idx < subclass_idx
    assert trans_idx < subclass_idx


def test_render_ce_inverse_role_and_nominal():
    # The one fragment dl.owl_functional.to_owl_functional_class_expression
    # REFUSES outright (see that module's docstring) -- this renderer must
    # cover it, since it is the whole reason this backend exists.
    names = _NameMap()
    concept = dl.Exists(InverseRole("hasChild"), Nominal("alice"))
    assert _render_ce(concept, names) == "ObjectSomeValuesFrom(ObjectInverseOf(:R1) ObjectOneOf(:I1))"


def test_render_ce_top_bottom_and_connectives():
    names = _NameMap()
    concept = dl.And(dl.Or(dl.Top(), dl.Not(dl.Atomic("A"))), dl.Bottom())
    assert (_render_ce(concept, names)
            == "ObjectIntersectionOf(ObjectUnionOf(owl:Thing ObjectComplementOf(:C1)) owl:Nothing)")


def test_render_ce_qualified_cardinality():
    names = _NameMap()
    concept = dl.AtLeast(2, "r", dl.Atomic("C"))
    assert _render_ce(concept, names) == "ObjectMinCardinality(2 :R1 :C1)"


def test_name_map_reuses_tokens_for_repeated_names():
    names = _NameMap()
    assert names.cls("Person") == ":C1"
    assert names.cls("Doctor") == ":C2"
    assert names.cls("Person") == ":C1"          # same kit name -> same token
    assert names.class_tokens() == [":C1", ":C2"]


def test_name_map_never_leaks_the_original_kit_name():
    # This kit's own DL glyph syntax (unicode ⊓, whitespace, ...) would not
    # survive an OWL PNAME_LN token -- the renderer must never emit the
    # ORIGINAL name string for exactly this reason (see the module
    # docstring's "Names" section).
    names = _NameMap()
    token = names.cls("Has Value ⊓ (Weird)")
    assert token == ":C1"
    assert "Has Value" not in token


# =============================================================================
# Non-live: hets_owl_available delegates to hets.docker.hets_available.
# =============================================================================

def test_hets_owl_available_delegates(monkeypatch):
    import unicode_fol_kit.hets.owl_backend as owl_backend_module

    monkeypatch.setattr(owl_backend_module, "hets_available", lambda: True)
    assert hets_owl_available() is True
    monkeypatch.setattr(owl_backend_module, "hets_available", lambda: False)
    assert hets_owl_available() is False


# =============================================================================
# Non-live: error paths, with the network calls monkeypatched away.
# =============================================================================

class _FakeClient:
    """Stands in for HetsClient: records the uploaded text, returns a
    caller-supplied canned goals list from consistency_check.
    """

    def __init__(self, goals):
        self._goals = goals
        self.uploaded = None

    def upload(self, text, filename):
        self.uploaded = text
        return "/tmp/fake/kit_owl_probe.ofn"

    def consistency_check(self, iri, node, *, reasoner, time_limit):
        assert reasoner == "Fact"          # never any other identifier -- see the module docstring
        return self._goals


def test_no_server_raises_backend_unavailable(monkeypatch):
    import unicode_fol_kit.hets.owl_backend as owl_backend_module

    def boom(*, start_container):
        raise BackendUnavailable("hets: no server discovered")

    monkeypatch.setattr(owl_backend_module, "discover_hets_url", boom)
    with pytest.raises(BackendUnavailable):
        external_concept_satisfiable(A)


def test_timeout_result_raises_hets_owl_error(monkeypatch):
    import unicode_fol_kit.hets.owl_backend as owl_backend_module

    fake = _FakeClient([{"result": "Timeout"}])
    monkeypatch.setattr(owl_backend_module, "HetsClient", lambda url, timeout: fake)
    monkeypatch.setattr(owl_backend_module, "discover_hets_url",
                         lambda *, start_container: ("http://fake:8000", None))
    with pytest.raises(HetsOwlError, match="Timeout"):
        external_concept_satisfiable(A)


def test_wrong_goal_count_raises_hets_owl_error(monkeypatch):
    import unicode_fol_kit.hets.owl_backend as owl_backend_module

    fake = _FakeClient([])
    monkeypatch.setattr(owl_backend_module, "HetsClient", lambda url, timeout: fake)
    monkeypatch.setattr(owl_backend_module, "discover_hets_url",
                         lambda *, start_container: ("http://fake:8000", None))
    with pytest.raises(HetsOwlError, match="1 goal"):
        external_concept_satisfiable(A)


def test_consistent_and_inconsistent_map_correctly(monkeypatch):
    import unicode_fol_kit.hets.owl_backend as owl_backend_module

    monkeypatch.setattr(owl_backend_module, "discover_hets_url",
                         lambda *, start_container: ("http://fake:8000", None))

    fake_true = _FakeClient([{"result": "Consistent"}])
    monkeypatch.setattr(owl_backend_module, "HetsClient", lambda url, timeout: fake_true)
    assert external_concept_satisfiable(A) is True

    fake_false = _FakeClient([{"result": "Inconsistent"}])
    monkeypatch.setattr(owl_backend_module, "HetsClient", lambda url, timeout: fake_false)
    assert external_concept_satisfiable(A) is False


def test_kb_consistent_always_passes_reasoner_fact(monkeypatch):
    # _FakeClient.consistency_check itself asserts reasoner == "Fact" (see
    # the module docstring's Phase-0 finding: an unset reasoner is broken
    # for OWL input in this image) -- this test just exercises that path.
    import unicode_fol_kit.hets.owl_backend as owl_backend_module

    fake = _FakeClient([{"result": "Consistent"}])
    monkeypatch.setattr(owl_backend_module, "HetsClient", lambda url, timeout: fake)
    assert _kb_consistent(None, dl.ABox(), time_limit=15, url="http://fake:8000") is True
    assert "Prefix(:=<" in fake.uploaded
    assert "Ontology(<http://unicode-fol-kit.invalid/hets-owl-probe>" in fake.uploaded


# =============================================================================
# Live: ALCHQ differential against dl.tableau (subset of
# tests/test_owl_reasoner.py's own hand-checked fixtures).
# =============================================================================

@hets_live
@live_hets
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
    assert external_concept_satisfiable(concept) is sat


@hets_live
@live_hets
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
    assert external_subsumes(sub, sup) is holds


@hets_live
@live_hets
def test_differential_tbox_and_abox():
    t = dl.TBox().add(A, B).add(B, C)
    assert dl.subsumes(A, C, t) is True
    assert external_subsumes(A, C, t) is True

    ab = dl.ABox().assert_concept("alice", A).assert_concept("alice", dl.Not(A))
    assert dl.abox_consistent(ab) is False
    assert external_abox_consistent(ab) is False


@hets_live
@live_hets
def test_differential_rbox_hierarchy_and_transitivity():
    # hasChild ⊑ hasDescendant, Trans(hasDescendant):
    # ∃hasChild.∃hasChild.C ⊑ ∃hasDescendant.C -- entailed purely by the RBox
    # (dl.tableau's own module-docstring example).
    t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant").add_transitive_role("hasDescendant")
    sub = dl.Exists("hasChild", dl.Exists("hasChild", C))
    sup = dl.Exists("hasDescendant", C)
    assert dl.subsumes(sub, sup, t) is True
    assert external_subsumes(sub, sup, t) is True
    # Negative control: without the RBox axioms, the same subsumption fails.
    assert dl.subsumes(sub, sup) is False
    assert external_subsumes(sub, sup) is False


@hets_live
@live_hets
def test_differential_qualified_number_restrictions():
    # >=2 r.T sqcap <=1 r.T is unsatisfiable (Hollunder & Baader's textbook
    # ALCQ clash: at least 2 pairwise-distinct r-successors but at most 1).
    clash = dl.And(dl.AtLeast(2, r, dl.Top()), dl.AtMost(1, r, dl.Top()))
    assert dl.concept_satisfiable(clash) is False
    assert external_concept_satisfiable(clash) is False
    # ABox-level: x has 2 DISTINCT r-successors in C, but is asserted <=1 r.C.
    ab = (dl.ABox().assert_concept("x", dl.AtMost(1, r, C))
          .assert_concept("y1", C).assert_concept("y2", C)
          .assert_role("x", "y1", r).assert_role("x", "y2", r)
          .assert_distinct("y1", "y2"))
    assert dl.abox_consistent(ab) is False
    assert external_abox_consistent(ab) is False
    # Same ABox WITHOUT the distinctness assertion: y1/y2 may denote the
    # same domain element (no unique name assumption), so it is consistent.
    ab2 = (dl.ABox().assert_concept("x", dl.AtMost(1, r, C))
           .assert_concept("y1", C).assert_concept("y2", C)
           .assert_role("x", "y1", r).assert_role("x", "y2", r))
    assert dl.abox_consistent(ab2) is True
    assert external_abox_consistent(ab2) is True


@hets_live
@live_hets
def test_differential_instance_check_and_retrieval():
    Human, Mortal = dl.Atomic("Human"), dl.Atomic("Mortal")
    t = dl.TBox().add(Human, Mortal)
    ab = dl.ABox().assert_concept("socrates", Human)
    assert dl.instance_check(ab, "socrates", Mortal, t) is True
    assert external_instance_check(ab, "socrates", Mortal, t) is True
    assert dl.instance_retrieval(ab, Mortal, t) == {"socrates"}
    assert external_instance_retrieval(ab, Mortal, t) == {"socrates"}


@hets_live
@live_hets
def test_differential_realize():
    Dog, Mammal, Animal = dl.Atomic("Dog"), dl.Atomic("Mammal"), dl.Atomic("Animal")
    t = dl.TBox().add(Dog, Mammal).add(Mammal, Animal)
    ab = dl.ABox().assert_concept("rex", Dog)
    vocabulary = [Animal, Mammal, Dog, dl.Top()]
    assert dl.realize(ab, "rex", vocabulary, t) == [Dog]
    assert external_realize(ab, "rex", vocabulary, t) == [Dog]
    assert dl.realize_all(ab, vocabulary, t) == external_realize_all(ab, vocabulary, t)


@hets_live
@live_hets
def test_three_way_agreement_with_dl_owl_reasoner_on_alchq():
    # The strong hand-checkable guarantee the roadmap's own test_oracle asks
    # for: on an ALCHQ case, THREE independently implemented routes
    # (in-house tableau, HermiT-via-owlready2, FaCT++-via-Hets) converge.
    # Also gated on owl_live: this specific test needs BOTH external routes.
    if not _owl_live_available():
        pytest.skip("owlready2 and/or a JVM (java on PATH) not found")
    from unicode_fol_kit.dl.owl_reasoner import external_subsumes as hermit_subsumes

    t = dl.TBox().add(A, B).add(B, C)
    assert dl.subsumes(A, C, t) is True
    assert hermit_subsumes(A, C, t) is True
    assert external_subsumes(A, C, t) is True


# =============================================================================
# Live: I/O textbook cases -- differential against dl.owl_reasoner (the only
# OTHER route that decides this fragment at all; dl.tableau refuses it).
# =============================================================================

@hets_live
@owl_live
@live_hets
@live_owl
def test_nominal_no_unique_name_assumption():
    from unicode_fol_kit.dl.owl_reasoner import external_concept_satisfiable as hermit_sat

    concept = dl.And(Nominal("a"), Nominal("b"))
    assert hermit_sat(concept) is True
    assert external_concept_satisfiable(concept) is True


@hets_live
@owl_live
@live_hets
@live_owl
def test_nominal_with_distinctness_is_unsatisfiable():
    from unicode_fol_kit.dl.owl_reasoner import external_abox_consistent as hermit_consistent

    ab = (dl.ABox().assert_concept("_probe", dl.And(Nominal("a"), Nominal("b")))
          .assert_distinct("a", "b"))
    assert hermit_consistent(ab) is False
    assert external_abox_consistent(ab) is False


@hets_live
@owl_live
@live_hets
@live_owl
def test_inverse_role_entailment_textbook_case():
    # (a, b):hasChild entails b : ExistsHasChild-inverse.Top (b has an
    # INCOMING hasChild edge, i.e. an hasChild-inverse successor, namely a).
    from unicode_fol_kit.dl.owl_reasoner import external_instance_check as hermit_instance_check

    ab = dl.ABox().assert_role("a", "b", "hasChild")
    query = dl.Exists(InverseRole("hasChild"), dl.Top())
    assert hermit_instance_check(ab, "b", query) is True
    assert external_instance_check(ab, "b", query) is True


@hets_live
@owl_live
@live_hets
@live_owl
def test_inverse_role_not_entailed_countermodel():
    # Negative control: only (a, c):hasChild -- b has NO incoming hasChild
    # edge, so the same query is NOT entailed for b.
    from unicode_fol_kit.dl.owl_reasoner import external_instance_check as hermit_instance_check

    ab = dl.ABox().assert_role("a", "c", "hasChild")
    query = dl.Exists(InverseRole("hasChild"), dl.Top())
    assert hermit_instance_check(ab, "b", query) is False
    assert external_instance_check(ab, "b", query) is False


@hets_live
@owl_live
@live_hets
@live_owl
def test_inverse_role_with_role_hierarchy_and_number_restriction():
    # Combines I with H: hasSon ⊑ hasChild, and (a,b):hasSon -- b's
    # inverse-hasChild successor set (via the hierarchy) includes a, so
    # Exists(hasChild-inverse, Top) is entailed for b even though only a
    # hasSon edge (never a literal hasChild edge) was ever asserted.
    from unicode_fol_kit.dl.owl_reasoner import external_instance_check as hermit_instance_check

    t = dl.TBox().add_role_inclusion("hasSon", "hasChild")
    ab = dl.ABox().assert_role("a", "b", "hasSon")
    query = dl.Exists(InverseRole("hasChild"), dl.Top())
    assert hermit_instance_check(ab, "b", query, t) is True
    assert external_instance_check(ab, "b", query, t) is True


@hets_live
@live_hets
def test_equivalent_agrees_with_dl_tableau_on_atomic_equivalence():
    # Deliberately NOT also compared against dl.owl_reasoner.external_equivalent
    # here: a genuine atomic<->atomic TBox.add_equivalence (two GCIs, A<=B
    # AND B<=A) makes owlready2 raise a raw "a __bases__ item causes an
    # inheritance cycle" TypeError (owlready2 models "is_a" as literal
    # Python class inheritance, so mutually-inclusive ATOMIC classes form a
    # cycle in ITS encoding) -- live-confirmed, out of scope to fix here
    # (dl/owl_reasoner.py is not owned by this change; see this task's
    # reported open_issues). This module's own OWL-text encoding has no such
    # restriction (SubClassOf is plain data, not a Python base-class edit),
    # so it decides this case correctly where that route currently cannot.
    t = dl.TBox().add_equivalence(A, B)
    assert dl.equivalent(A, B, t) is True
    assert external_equivalent(A, B, t) is True
    assert external_concept_unsatisfiable(dl.Bottom()) is True
