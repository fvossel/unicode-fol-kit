r"""One name, two kinds OWL 2 DL keeps apart: refused, never conflated.

OWL 2 DL (Structural Specification, section 5.8.1) forbids an IRI that is both an
object property and a data property, and one that is both a class and a datatype.
The kit's stored axioms keep the kinds apart (``TBox.functional_roles`` and
``TBox.functional_data_properties`` are different fields), but its first-order
image has ONE predicate per name, so ``P(x, y)`` for an object property and
``P(x, v)`` for a data property are the same predicate and the image changes what
follows. The image therefore REFUSES the pair by name, before building anything.

Hand-derived expectations
-------------------------
The knowledge base ``FunctionalDataProperty(P)``, ``A ⊑ ∃P.B`` (an OBJECT
restriction), ``A ⊑ ∃P.xsd:integer`` (a DATA restriction), ``a : A``:

* read as OWL 2 reads it (two different properties that merely share a spelling,
  here only to show what the conflation destroys): ``a`` needs one object
  successor in ``B`` and one data value, which are different things, so the
  knowledge base is CONSISTENT;
* conflated onto one predicate ``P``: ``a`` has a ``P``-value that is an object of
  ``B`` and one that is an integer, and ``FunctionalDataProperty(P)`` says a
  ``P``-value is unique, so the two are one value -- which the two-sorted axioms
  forbid being both an object and a datum. INCONSISTENT. (The old image printed
  exactly that and ``api.prove`` answered ``proved``.)

With the data property renamed ``PD`` the conflation is gone, and the same
question is answered ``refuted`` (a model exists: ``a`` with a ``P``-successor
in ``B`` and a ``PD``-value ``0``).
"""

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit import api
from unicode_fol_kit.dl.datatypes import Datatype, Literal, UnsupportedDatatypeError
from unicode_fol_kit.fol.nodes import Not as FNot

A, B = dl.Atomic("A"), dl.Atomic("B")
INT = Datatype("xsd:integer")
TIMEOUT_MS = 60000


def _pun(data_name):
    """The knowledge base above, the data property spelled ``data_name``."""
    tbox = dl.TBox().add_functional_data_property(data_name)
    tbox.add(A, dl.Exists("P", B))
    tbox.add(A, dl.DataExists(data_name, INT))
    return tbox, dl.ABox().assert_concept("a", A)


def test_the_conflated_knowledge_base_is_refused_by_name_not_proved_inconsistent():
    tbox, abox = _pun("P")
    with pytest.raises(UnsupportedDatatypeError) as info:
        dl.kb_to_fol(tbox, abox)
    message = str(info.value)
    assert "'P'" in message
    assert "object property" in message and "data property" in message
    assert "OWL 2 DL" in message and "Rename" in message


@pytest.mark.parametrize("separation", ["two-sorted", "data-lattice", "none"])
def test_every_separation_refuses_it(separation):
    # The predicate is shared whatever the sort discipline: 'none' only drops
    # the sort axioms, not the conflation.
    tbox, abox = _pun("P")
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.kb_to_fol(tbox, abox, separation=separation)
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.data_sort_axioms(tbox, abox, separation=separation)


def test_the_renamed_data_property_is_consistent_and_still_answered():
    # control: no pun, a model exists -> 'refuted' (the negated knowledge base
    # is not valid).
    tbox, abox = _pun("PD")
    kb = dl.kb_to_fol(tbox, abox)
    assert api.prove(FNot(kb.formula), list(kb.axioms), timeout=TIMEOUT_MS).status == "refuted"


def test_the_data_box_alone_refuses_a_pun_that_the_tbox_holds():
    # databox_to_fol renders the data box only, but the vocabulary of the whole
    # TBox decides whether its predicates are conflated: P is a role in the
    # concept inclusion and a data property in the functional axiom.
    tbox, _abox = _pun("P")
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.databox_to_fol(tbox)


def test_an_abox_alone_can_pun_too():
    # (a, b) : P  and  P(a, 1): ground atoms P(a, b) and P(a, 1) of ONE predicate.
    abox = dl.ABox().assert_role("a", "b", "P").assert_data("a", "P", Literal("1", "xsd:integer"))
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.abox_to_fol(abox)
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.kb_to_fol(None, abox)


def test_a_class_and_a_datatype_with_one_name_are_refused():
    # Digit as a class (Digit ⊑ A) and as a datatype (Digit ≡ xsd:integer) would
    # be the one predicate Digit(·) used for an individual and for a value.
    tbox = dl.TBox().add(dl.Atomic("Digit"), A).add_datatype_definition("Digit", INT)
    with pytest.raises(UnsupportedDatatypeError) as info:
        dl.kb_to_fol(tbox, dl.ABox())
    assert "'Digit'" in str(info.value)
    assert "class" in str(info.value) and "datatype" in str(info.value)


def test_a_class_spelled_like_a_builtin_datatype_is_refused_in_either_spelling():
    # xsd:integer written as the full IRI is the SAME datatype as xsd:integer
    # (canonical_datatype_name), so a class by that name is the pun too.
    long = "http://www.w3.org/2001/XMLSchema#integer"
    for class_name in ("xsd:integer", long):
        tbox = (dl.TBox().add(dl.Atomic(class_name), A)
                .add_data_property_range("p", INT))
        with pytest.raises(UnsupportedDatatypeError, match="class"):
            dl.kb_to_fol(tbox, dl.ABox())


def test_the_punning_that_owl_2_dl_allows_is_still_accepted():
    # OWL 2 DL allows a class, an object property and an individual to share an
    # IRI (only object/data property and class/datatype are forbidden pairs), so
    # the image keeps accepting them: refusing more than OWL 2 forbids would be a
    # regression for every ontology that punned this way.
    tbox = (dl.TBox().add(dl.Atomic("x"), dl.Exists("x", dl.Atomic("x")))
            .add_data_property_range("d", INT))
    abox = dl.ABox().assert_concept("x", dl.Atomic("x")).assert_role("x", "x", "x")
    kb = dl.kb_to_fol(tbox, abox)
    assert kb.separation == "two-sorted"
