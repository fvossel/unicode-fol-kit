"""The external OWL route refuses what the kit refuses before it asks for ``owlready2``.

A role box that breaks OWL 2's simple-role restriction is refused by the kit's own check,
``NonSimpleRoleError``, on every route: a transitive role is not simple, and an asymmetry or a
functionality axiom may only name a simple role (OWL 2 Structural Specification, section 11.2).
On the external route that check ran after the lookup of the optional package, so on a machine
without ``owlready2`` the same knowledge base was refused with "owlready2 is not installed":
another error for one input, depending on what is installed. The order is the kit's own
refusals first, then the package. A knowledge base the kit accepts is still answered with the
missing package, since nothing can decide it without the reasoner.

The package is made absent here by replacing the module's ``available``, which is what a
machine without the ``owl`` extra reports.
"""

import pytest

import unicode_logic_kit.dl as dl
import unicode_logic_kit.dl.owl_reasoner as owl_reasoner

A, B = dl.Atomic("A"), dl.Atomic("B")


@pytest.fixture()
def without_owlready2(monkeypatch):
    monkeypatch.setattr(owl_reasoner, "available", lambda: False)


def _transitive_and_asymmetric():
    return dl.TBox().add_transitive_role("r").add_asymmetric_role("r")


def _transitive_and_functional():
    return dl.TBox().add_transitive_role("r").add_functional_role("r")


def _one_assertion():
    return dl.ABox().assert_concept("bob", A)


ENTRY_POINTS = {
    "concept_satisfiable": lambda tbox: dl.external_concept_satisfiable(A, tbox),
    "concept_unsatisfiable": lambda tbox: dl.external_concept_unsatisfiable(A, tbox),
    "subsumes": lambda tbox: dl.external_subsumes(A, B, tbox),
    "equivalent": lambda tbox: dl.external_equivalent(A, B, tbox),
    "abox_consistent": lambda tbox: dl.external_abox_consistent(_one_assertion(), tbox),
    "instance_check": lambda tbox: dl.external_instance_check(_one_assertion(), "bob", B, tbox),
    "instance_retrieval": lambda tbox: dl.external_instance_retrieval(_one_assertion(), B, tbox),
    "realize": lambda tbox: dl.external_realize(_one_assertion(), "bob", [A, B], tbox),
    "realize_all": lambda tbox: dl.external_realize_all(_one_assertion(), [A, B], tbox),
}


@pytest.mark.parametrize("entry", sorted(ENTRY_POINTS))
def test_a_role_box_the_kit_refuses_is_refused_with_the_kits_error_without_the_package(
        entry, without_owlready2):
    with pytest.raises(dl.NonSimpleRoleError, match="AsymmetricObjectProperty"):
        ENTRY_POINTS[entry](_transitive_and_asymmetric())
    with pytest.raises(dl.NonSimpleRoleError, match="FunctionalObjectProperty"):
        ENTRY_POINTS[entry](_transitive_and_functional())


@pytest.mark.parametrize("entry", sorted(ENTRY_POINTS))
def test_a_knowledge_base_the_kit_accepts_is_answered_with_the_missing_package(
        entry, without_owlready2):
    with pytest.raises(owl_reasoner.OwlReasonerError, match="owlready2 is not installed"):
        ENTRY_POINTS[entry](dl.TBox())


def test_the_refusal_names_the_role(without_owlready2):
    with pytest.raises(dl.NonSimpleRoleError, match="'r'"):
        dl.external_abox_consistent(dl.ABox(), _transitive_and_asymmetric())
