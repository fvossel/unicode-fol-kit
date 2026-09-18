"""Tests for the external OWL 2 DL reasoner backend (unicode_fol_kit.dl.owl_reasoner).

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

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl.owl_reasoner import available

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
    import unicode_fol_kit.dl.owl_reasoner as owl_reasoner_module

    real_find_spec = importlib.util.find_spec

    def fake_find_spec(name, *a, **kw):
        if name == "owlready2":
            return None
        return real_find_spec(name, *a, **kw)

    monkeypatch.setattr(owl_reasoner_module.importlib.util, "find_spec", fake_find_spec)
    assert owl_reasoner_module.available() is False


def test_unavailable_raises_owl_reasoner_error(monkeypatch):
    import unicode_fol_kit.dl.owl_reasoner as owl_reasoner_module

    monkeypatch.setattr(owl_reasoner_module, "available", lambda: False)
    with pytest.raises(owl_reasoner_module.OwlReasonerError, match="owlready2"):
        owl_reasoner_module.external_concept_satisfiable(A)


def test_all_individuals_helper():
    # _all_individuals mirrors dl.tableau._individuals's own convention (see
    # test_dl_alc.py's test_instance_and_realize_edge_cases for the tableau
    # side of this same contract): a role-only individual still counts, and a
    # wholly empty ABox falls back to {"a"}.
    from unicode_fol_kit.dl.owl_reasoner import _all_individuals

    ab = dl.ABox().assert_role("alice", "bob", "hasChild")
    assert _all_individuals(ab) == {"alice", "bob"}
    assert _all_individuals(dl.ABox()) == {"a"}


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
