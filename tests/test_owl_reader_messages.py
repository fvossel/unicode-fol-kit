r"""The smaller items of the OWL layer: the refusal names the renderer that renders
the data box, the Hets sweep reads the same individuals as every other route, and
the strict and the lenient reader say what they consume or refuse.

``tbox_to_fol`` and the data box
--------------------------------
``tbox_to_fol`` refuses a TBox that carries side axioms and points at the
renderers of the side axioms. The ROLE box is ``rbox_to_fol``'s; the DATA box is
``databox_to_fol``'s, and ``rbox_to_fol`` of a TBox with data axioms alone is the
tautology (its role box is empty), so a message that named only ``rbox_to_fol``
sent a caller to a function that renders nothing of what was refused. The
message now names ``databox_to_fol`` exactly when the TBox carries a data-box
axiom, and a TBox with role-box axioms alone gets the message it always had.

The sweeps' individuals (the tests are in ``tests/test_hets_owl_probe.py``)
---------------------------------------------------------------------------
``instance_retrieval`` and ``realize_all`` sweep the individuals the ABox NAMES
(``dl.tableau._abox_individual_names``, driven by the axiom-kind table) with no
fallback: an ABox that names nobody has nobody to retrieve. The anonymous ``"a"``
fallback of ``dl.tableau._individuals`` is for ``abox_consistent`` only -- the
node a TBox has to run on -- and the HermiT route already reads the fallback-free
scan. The Hets route read ``_individuals``, so over an empty ABox it asked
FaCT++ about a phantom individual and reported it as a member:
``TBox().add(⊤, A)`` with an empty ABox retrieved ``{"a"}`` there and ``set()``
from the tableau and from HermiT.
"""

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit.dl import tableau as dl_tableau
from unicode_logic_kit.dl.datatypes import Datatype
from unicode_logic_kit.dl.owl_functional import parse_owl_functional, parse_owl_functional_axioms

A = dl.Atomic("A")
INT = Datatype("xsd:integer")


# --------------------------------------------------------------------------- #
# tbox_to_fol's refusal names the renderer of the data box
# --------------------------------------------------------------------------- #

#: The value one stored axiom of each TBox field takes. A field the dataclass
#: has and this dict lacks FAILS the derived tests below by name.
_STORED = {
    "inclusions": (A, A),
    "role_inclusions": ("r", "s"),
    "transitive_roles": "r",
    "inverse_role_pairs": ("r", "s"),
    "role_chains": (("r", "s"), "t"),
    "disjoint_role_pairs": ("r", "s"),
    "symmetric_roles": "r",
    "asymmetric_roles": "r",
    "reflexive_roles": "r",
    "irreflexive_roles": "r",
    "functional_roles": "r",
    "inverse_functional_roles": "r",
    "role_domains": ("r", A),
    "role_ranges": ("r", A),
    "data_property_inclusions": ("d", "e"),
    "disjoint_data_property_pairs": ("d", "e"),
    "functional_data_properties": "d",
    "data_property_domains": ("d", A),
    "data_property_ranges": ("d", INT),
    "datatype_definitions": ("D", INT),
}


def _tbox_with_one(field_name):
    assert field_name in _STORED, f"TBox.{field_name} has no sample here: add one"
    tbox = dl.TBox()
    stored = getattr(tbox, field_name)
    (stored.add if isinstance(stored, set) else stored.append)(_STORED[field_name])
    return tbox


_SIDE_ROWS = [row for row in dl_tableau._AXIOM_KINDS
              if row.holder == "tbox" and row.part == "side"]


def test_every_side_row_has_a_sample():
    assert _SIDE_ROWS, "the axiom-kind table has no TBox side rows?"
    for row in _SIDE_ROWS:
        assert row.field in _STORED, f"{row.kind} ({row.field}): add a sample"


@pytest.mark.parametrize("row", _SIDE_ROWS, ids=lambda row: row.kind)
def test_the_refusal_names_the_renderer_that_renders_what_it_refused(row):
    with pytest.raises(dl.RoleBoxOmittedError) as info:
        dl.tbox_to_fol(_tbox_with_one(row.field))
    message = str(info.value)
    assert row.kind in message
    for pointer in ("kb_to_fol", "concept_inclusions_only"):
        assert pointer in message
    if row.layer == "data":
        assert "databox_to_fol" in message
    else:
        # a role-box axiom alone: the message is the one it always was
        assert "rbox_to_fol" in message
        assert "databox_to_fol" not in message


def test_a_tbox_with_both_boxes_names_both_renderers():
    tbox = dl.TBox().add_transitive_role("r").add_functional_data_property("d")
    with pytest.raises(dl.RoleBoxOmittedError) as info:
        dl.tbox_to_fol(tbox)
    message = str(info.value)
    assert "rbox_to_fol" in message and "databox_to_fol" in message


def test_the_renderer_the_message_names_renders_what_was_refused():
    # hand-derived: FunctionalDataProperty(d) is  ∀x ∀v ∀w (d(x, v) ∧ d(x, w) → v = w),
    # databox_to_fol's image; rbox_to_fol's role box is empty -> a tautology
    tbox = dl.TBox().add_functional_data_property("d")
    assert "d(x, v)" in dl.databox_to_fol(tbox).to_unicode_str()
    assert "d(" not in dl.rbox_to_fol(tbox).to_unicode_str()


# --------------------------------------------------------------------------- #
# The strict reader's docstring says what it consumes without a word
# --------------------------------------------------------------------------- #

_CONSUMED = [
    "SubAnnotationPropertyOf(label rdfs:label)",
    "AnnotationPropertyDomain(label A)",
    "AnnotationPropertyRange(label B)",
    "SubObjectPropertyOf(r owl:topObjectProperty)",
    "SubObjectPropertyOf(owl:bottomObjectProperty r)",
    "SubDataPropertyOf(d owl:topDataProperty)",
]


@pytest.mark.parametrize("axiom", _CONSUMED)
def test_the_strict_reader_consumes_these_silently_and_the_lenient_one_reports_them(axiom):
    text = f"Ontology(\n  {axiom}\n)"
    # strict: nothing is raised and nothing is read ...
    assert parse_owl_functional(text) == (dl.TBox(), dl.ABox())
    # ... lenient: the same axiom, REPORTED
    result = parse_owl_functional_axioms(text)
    assert result.ok and result.accepted == 0
    (consumed,) = result.consumed
    assert consumed.keyword == axiom.split("(")[0]


def test_the_strict_readers_docstring_says_so():
    doc = parse_owl_functional.__doc__
    for keyword in ("SubAnnotationPropertyOf", "AnnotationPropertyDomain",
                    "AnnotationPropertyRange", "owl:topObjectProperty",
                    "parse_owl_functional_axioms"):
        assert keyword in doc, f"parse_owl_functional's docstring does not mention {keyword}"
    assert "without a report" in doc


def test_the_lenient_readers_docstring_states_its_two_limits():
    doc = parse_owl_functional_axioms.__doc__
    # 'accepted' does not mean 'translatable' for a whole knowledge base;
    # and the recursion limit
    assert "RecursionError" in doc
    assert "to_kb" in doc


def test_a_class_expression_nested_past_the_recursion_limit_raises_recursion_error():
    # Documented, not rewritten: the reader is recursive descent, so a class
    # expression nested more deeply than Python's recursion limit allows is a
    # RecursionError, never a silent truncation.
    depth = 2000
    text = ("Ontology(SubClassOf(A " + "ObjectComplementOf(" * depth + "B"
            + ")" * depth + "))")
    with pytest.raises(RecursionError):
        parse_owl_functional_axioms(text)
