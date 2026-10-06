r"""The individuals of an ABox include the ones named INSIDE an asserted class
expression.

``ABox().assert_concept("a", HasValue("r", "b"))`` makes ``b`` a constant of the
FOL image (``r(a, b)``) and a named individual of the knowledge base, but the
scan behind ``KnowledgeBaseFOL.individuals`` and behind the sweeps of
``instance_retrieval``/``realize_all`` read only the assertion's SUBJECT, so
``b`` was in neither: ``kb.individuals == ("a",)``. An individual named in an
ABox assertion is an individual of the ABox wherever in the assertion it stands.
The fillers of a TBox's class expressions stay as documented (they are constants
of the image, and not things the knowledge base makes assertions about).

The in-house tableau refuses a nominal and a value restriction by name, so what
changes is ``kb.individuals`` and the external routes' sweeps — which read the
same scan, so one scan is tested here and the two readers against it.
"""

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl import tableau as _tableau
from unicode_fol_kit.fol.nodes import Constant

A, B = dl.Atomic("A"), dl.Atomic("B")


def _constants(node) -> set:
    return {n.name for n in node.walk() if isinstance(n, Constant)}


@pytest.mark.parametrize("build, expected", [
    # a : ∃r.{b}  names a (the subject) and b (the filler of the value restriction)
    (lambda: dl.ABox().assert_concept("a", dl.HasValue("r", "b")), ("a", "b")),
    # a nominal at the top, and under a negation, a conjunction, an existential
    (lambda: dl.ABox().assert_concept("a", dl.Nominal("b")), ("a", "b")),
    (lambda: dl.ABox().assert_concept(
        "c", dl.Not(dl.And(A, dl.Exists("r", dl.Nominal("d"))))), ("c", "d")),
    # several, at several depths, in several assertions; sorted, once each
    (lambda: (dl.ABox().assert_concept("z", dl.ForAll("r", dl.HasValue("s", "m")))
              .assert_concept("a", dl.Or(dl.Nominal("m"), dl.AtLeast(2, "r", dl.HasValue("s", "k"))))),
     ("a", "k", "m", "z")),
    # a data restriction names no individual
    (lambda: dl.ABox().assert_concept(
        "a", dl.DataExists("d", dl.Datatype("xsd:integer"))), ("a",)),
    # no class expression with an individual: the subject and the role endpoints
    (lambda: dl.ABox().assert_concept("a", A).assert_role("b", "c", "r"), ("a", "b", "c")),
], ids=["has-value", "nominal", "nested-nominal", "several", "data", "unchanged"])
def test_kb_individuals_lists_every_individual_an_abox_assertion_names(build, expected):
    abox = build()
    kb = dl.kb_to_fol(None, abox)
    assert kb.individuals == expected
    # one scan: the shared one the sweeps of the routes read says the same
    assert sorted(_tableau._abox_individual_names(abox)) == list(expected)
    assert sorted(dl.owl_reasoner._all_individuals(abox)) == list(expected)


def test_every_individual_listed_is_a_constant_of_the_image():
    # The claim behind "listed": it IS a constant of the image, which is what a
    # goal about the individual has to use (a : ∃r.{b} is r(a, b), a ground atom).
    abox = dl.ABox().assert_concept("a", dl.HasValue("r", "b"))
    kb = dl.kb_to_fol(None, abox)
    assert kb.abox.to_unicode_str() == "r(a, b)"
    assert set(kb.individuals) <= _constants(kb.abox)


def test_the_fillers_of_a_tbox_class_expression_stay_out():
    # C ⊑ ∃r.{z} makes z a constant of the image, but the knowledge base asserts
    # nothing ABOUT z, so it is not in `individuals` (documented, deliberate).
    tbox = dl.TBox().add(A, dl.HasValue("r", "z"))
    kb = dl.kb_to_fol(tbox, dl.ABox().assert_concept("a", A))
    assert kb.individuals == ("a",)
    assert "z" in _constants(kb.formula)


def test_the_in_house_tableau_still_refuses_what_it_always_refused():
    # Nothing is decided differently in house: a value restriction and a nominal
    # are refused by name, wherever in an assertion they stand.
    with pytest.raises(dl.UnsupportedConceptError, match="ObjectHasValue"):
        dl.abox_consistent(dl.ABox().assert_concept("a", dl.HasValue("r", "b")))
    with pytest.raises(dl.UnsupportedConceptError, match="Nominal"):
        dl.abox_consistent(dl.ABox().assert_concept("a", dl.Exists("r", dl.Nominal("b"))))
