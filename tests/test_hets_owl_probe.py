r"""The Hets/FaCT++ route's probe ABox and its individual sweep (offline).

Two defects of one family, both silent: ``hets.owl_backend`` rebuilt the
instance-check probe ABox FIELD BY FIELD (so ``same_assertions`` and
``negative_role_assertions`` never reached FaCT++, and a field added later would
not either), and it swept individuals with a hand-written scan that did not read
those same two fields. Every ``external_instance_*`` / ``external_realize*``
answer was then about a strictly WEAKER knowledge base than the one the caller
handed in.

Nothing here needs a Hets server: the probe is compared structurally, the
document the route would upload is read as text, and the network is replaced by
a fake client that records what it was sent.

How the expected values are derived (never copied from the code's output)
-------------------------------------------------------------------------
* The probe of ``abox`` for ``individual : concept`` is, by the entailment
  reduction the module documents, ``abox`` plus the ONE assertion
  ``individual : ¬concept`` and nothing else removed: every other field is
  carried over unchanged.
* ``_render_document`` allocates synthetic names in the order it visits the
  axioms (classes ``:C<n>``, roles ``:R<n>``, data properties ``:P<n>``,
  individuals ``:I<n>``), and visits concept assertions, role assertions,
  distinctness, sameness, negative role assertions, then data assertions. So
  for the ABox below ``a : A`` allocates ``:C1`` and ``:I1``; the probe's
  ``b : ¬A`` allocates ``:I2``; ``≠(b, c)`` allocates ``:I3``; the negative
  assertion allocates ``:R1``; the data assertion allocates ``:P1``.
* The individuals an ABox mentions are the names it contains, whatever the
  assertion kind: ``same(x, y)`` and ``¬r(p, q)`` mention x, y, p and q.
"""

import dataclasses

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl import tableau as dl_tableau
from unicode_fol_kit.dl.datatypes import Literal
from unicode_fol_kit.hets import owl_backend
from unicode_fol_kit.hets.owl_backend import (
    _abox_with, _all_individuals, _render_document,
    external_instance_check, external_instance_retrieval, external_realize_all,
)

A = dl.Atomic("A")


# =============================================================================
# [3] the probe ABox carries EVERY field.
# =============================================================================

def _fields_the_probe_dropped(make_probe):
    """The names of the ABox fields whose assertions ``make_probe(abox)`` lost,
    derived from ``dataclasses.fields(ABox)`` and not from a list of names, so
    a field added to the dataclass tomorrow is checked tomorrow without anyone
    editing this function.

    Each field gets ONE opaque marker, put straight into its list: a correct
    copy cannot look inside an assertion, so a marker that arrives proves the
    field was carried and one that does not proves it was dropped.
    """
    abox = dl.ABox()
    markers = {}
    for f in dataclasses.fields(dl.ABox):
        stored = getattr(abox, f.name)
        assert isinstance(stored, list), (
            f"ABox.{f.name} is not a list: teach this test the new storage")
        markers[f.name] = ("marker", f.name)
        stored.append(markers[f.name])
    probe = make_probe(abox)
    return {name for name, marker in markers.items()
            if marker not in getattr(probe, name)}


def test_the_probe_abox_keeps_every_field_of_the_abox():
    assert _fields_the_probe_dropped(lambda abox: _abox_with(abox, "i", A)) == set()


def test_the_check_would_flag_a_field_by_field_probe_and_names_the_dropped_fields():
    """The checker above is not vacuous: the shape this function had until
    0.30.0 (three fields, rebuilt by hand) drops EVERY OTHER field, whichever
    they are. That set is derived, so it grows with the dataclass."""
    def legacy_probe(abox):
        return dl.ABox(
            concept_assertions=abox.concept_assertions + [("i", A)],
            role_assertions=list(abox.role_assertions),
            distinct_assertions=list(abox.distinct_assertions),
        )

    carried = {"concept_assertions", "role_assertions", "distinct_assertions"}
    every_field = {f.name for f in dataclasses.fields(dl.ABox)}
    dropped = _fields_the_probe_dropped(legacy_probe)
    assert dropped == every_field - carried
    # ... which on today's dataclass includes the two OWL 2 identity fields
    assert {"same_assertions", "negative_role_assertions"} <= dropped


def test_the_probe_adds_exactly_one_assertion_and_never_aliases_the_original():
    abox = dl.ABox().assert_concept("a", A).assert_same("a", "b")
    before = {f.name: list(getattr(abox, f.name)) for f in dataclasses.fields(dl.ABox)}
    probe = _abox_with(abox, "b", dl.Not(A))
    # one extra concept assertion, appended last ...
    assert probe.concept_assertions == [("a", A), ("b", dl.Not(A))]
    # ... every other list equal to the original's ...
    for f in dataclasses.fields(dl.ABox):
        if f.name != "concept_assertions":
            assert getattr(probe, f.name) == before[f.name], f.name
    # ... and the original untouched, with no list shared (mutating the probe
    # must not reach back).
    for f in dataclasses.fields(dl.ABox):
        assert getattr(abox, f.name) == before[f.name], f.name
        assert getattr(probe, f.name) is not getattr(abox, f.name), f.name


def _identity_abox():
    """``a : A``, ``a = b``, ``b ≠ c``, ``¬r(a, c)`` and ``d(a, 1)``: a concept
    and a distinctness assertion (the two kinds the old probe kept) next to the
    sameness, negative role and data assertions it dropped."""
    return (dl.ABox()
            .assert_concept("a", A)
            .assert_same("a", "b")
            .assert_distinct("b", "c")
            .assert_negative_role("a", "c", "r")
            .assert_data("a", "d", Literal("1", "xsd:integer")))


def test_the_probe_document_carries_each_identity_and_data_assertion():
    probe = _abox_with(_identity_abox(), "b", dl.Not(A))
    lines = {line.strip() for line in _render_document(dl.TBox(), probe).splitlines()}
    # hand-derived (see the module docstring for the name allocation)
    assert "ClassAssertion(:C1 :I1)" in lines                          # a : A
    assert "ClassAssertion(ObjectComplementOf(:C1) :I2)" in lines      # b : ¬A, the probe
    assert "DifferentIndividuals(:I2 :I3)" in lines                    # b ≠ c
    assert "SameIndividual(:I1 :I2)" in lines                          # a = b
    assert "NegativeObjectPropertyAssertion(:R1 :I1 :I3)" in lines     # ¬r(a, c)
    assert 'DataPropertyAssertion(:P1 :I1 "1"^^xsd:integer)' in lines  # d(a, 1)


# --- end to end through the (fake) client ------------------------------------

class _RecordingClient:
    """Stands in for ``HetsClient``: records every uploaded document and answers
    every consistency check with ``result``."""

    def __init__(self, result):
        self.result = result
        self.uploads = []

    def upload(self, text, filename):
        self.uploads.append(text)
        return "/tmp/fake/kit_owl_probe.ofn"

    def consistency_check(self, iri, node, *, reasoner, time_limit):
        return [{"result": self.result}]


@pytest.fixture
def hets_says(monkeypatch):
    """``hets_says("Inconsistent")`` -> the fake client every check will use."""
    def install(result):
        fake = _RecordingClient(result)
        monkeypatch.setattr(owl_backend, "HetsClient", lambda url, timeout: fake)
        monkeypatch.setattr(owl_backend, "discover_hets_url",
                            lambda *, start_container: ("http://fake:8000", None))
        return fake
    return install


def test_external_instance_check_uploads_the_identity_assertions(hets_says):
    fake = hets_says("Inconsistent")
    assert external_instance_check(_identity_abox(), "b", A) is True
    assert len(fake.uploads) == 1
    document = fake.uploads[0]
    assert "SameIndividual(:I1 :I2)" in document
    assert "NegativeObjectPropertyAssertion(:R1 :I1 :I3)" in document
    assert 'DataPropertyAssertion(:P1 :I1 "1"^^xsd:integer)' in document


# =============================================================================
# [13] the sweep reads every assertion kind, from the same source as the others.
# =============================================================================

def test_an_individual_that_occurs_only_in_an_identity_assertion_is_swept():
    # hand-derived: x, y from same(x, y); p, q from ¬r(p, q). Before, the scan
    # saw neither list and fell back to the phantom "a".
    abox = dl.ABox().assert_same("x", "y").assert_negative_role("p", "q", "r")
    assert _all_individuals(abox) == {"p", "q", "x", "y"}


def test_an_abox_that_names_nobody_sweeps_nobody():
    # The anonymous "a" of dl.tableau._individuals is the node abox_consistent
    # runs the TBox on; it is not an individual of the knowledge base, and the
    # sweeps (instance_retrieval, realize_all) never report it -- the tableau and
    # the HermiT route read the same fallback-free scan, so this route does too.
    assert _all_individuals(dl.ABox()) == set()
    assert _all_individuals(dl.ABox().assert_same("x", "y")) == {"x", "y"}


def test_the_hets_sweep_never_retrieves_the_phantom_individual(hets_says):
    # TBox ⊤ ⊑ A over an ABox that names nobody. Every probe the fake server
    # answers "Inconsistent", i.e. "entailed", so the ONLY thing that can keep a
    # name out of the answer is the sweep itself: it must enumerate no one. The
    # tableau's answers, by the definition in dl.tableau (an ABox that names
    # nobody has nobody to retrieve or realize) are set() and {}.
    tbox = dl.TBox().add(dl.Top(), A)
    hets_says("Inconsistent")
    assert dl.instance_retrieval(dl.ABox(), A, tbox) == set()
    assert dl.realize_all(dl.ABox(), [A], tbox) == {}
    assert external_instance_retrieval(dl.ABox(), A, tbox) == set()
    assert external_realize_all(dl.ABox(), [A], tbox) == {}


def test_retrieval_and_realize_all_sweep_those_individuals(hets_says):
    hets_says("Inconsistent")                  # every probe "entails" the concept
    abox = dl.ABox().assert_same("x", "y").assert_negative_role("p", "q", "r")
    assert external_instance_retrieval(abox, A) == {"p", "q", "x", "y"}
    assert set(external_realize_all(abox, [])) == {"p", "q", "x", "y"}


#: The shape one stored assertion of each ABox field takes, as a function of the
#: individual names it mentions (one per entry of the row's
#: ``individual_positions``, in order). A field the axiom-kind table has and this
#: dict lacks FAILS the test below by name: that is the prompt to add its shape.
_STORED_SHAPES = {
    "concept_assertions": lambda n: (n[0], A),
    "role_assertions": lambda n: (n[0], n[1], "r"),
    "distinct_assertions": lambda n: (n[0], n[1]),
    "same_assertions": lambda n: (n[0], n[1]),
    "negative_role_assertions": lambda n: (n[0], n[1], "r"),
    "data_assertions": lambda n: (n[0], "d", Literal("1", "xsd:integer")),
    "negative_data_assertions": lambda n: (n[0], "d", Literal("1", "xsd:integer")),
}


def _abox_with_one_item_per_kind(*, object_layer_only):
    """An ABox with one assertion in EVERY ``abox`` row of the axiom-kind table
    that mentions an individual (or every object-layer row), each individual
    slot carrying a name no other slot shares, and the set of names so used.
    Driven by the table, so a kind added later is covered by its row."""
    abox = dl.ABox()
    expected = set()
    for row in dl_tableau._AXIOM_KINDS:
        if row.holder != "abox" or not row.individual_positions:
            continue
        if object_layer_only and row.layer == "data":
            continue
        assert row.field in _STORED_SHAPES, (
            f"ABox.{row.field} ({row.kind}) has no sample shape here: add one")
        names = [f"{row.field}_{i}" for i in range(len(row.individual_positions))]
        stored = _STORED_SHAPES[row.field](names)
        assert [stored[p] for p in row.individual_positions] == names, (
            f"the sample for {row.field} does not put the names at "
            f"individual_positions={row.individual_positions}")
        getattr(abox, row.field).append(stored)
        expected.update(names)
    return abox, expected


def test_the_document_renders_exactly_one_axiom_for_every_abox_field():
    """The probe now carries every field; the RENDERER must write every field
    too, or an assertion kind added to the ABox reaches ``_abox_with`` and is
    then silently left out of the uploaded document. Derived from
    ``dataclasses.fields(ABox)``: one stored assertion per field, so exactly one
    axiom line (a ``Declaration`` is not an axiom)."""
    for f in dataclasses.fields(dl.ABox):
        row = next(r for r in dl_tableau._AXIOM_KINDS
                   if r.holder == "abox" and r.field == f.name)
        assert f.name in _STORED_SHAPES, (
            f"ABox.{f.name} has no sample shape here: add one")
        names = [f"i{n}" for n in range(len(row.individual_positions))]
        abox = dl.ABox()
        getattr(abox, f.name).append(_STORED_SHAPES[f.name](names))
        body = [line.strip() for line in _render_document(dl.TBox(), abox).splitlines()
                if line.startswith("  ")]
        axioms = [line for line in body if not line.startswith("Declaration(")]
        assert len(axioms) == 1, (f.name, body)


def test_the_sweep_is_the_table_driven_scan_of_the_other_routes():
    """One source for every route: this sweep, the tableau's two sweeps, the
    HermiT route's and the FOL image's ``KnowledgeBaseFOL.individuals`` cannot
    drift apart -- for one stored assertion of EVERY ABox row of the table (the
    data rows included), and for the ABox that names nobody."""
    from unicode_fol_kit.dl import owl_reasoner

    abox, expected = _abox_with_one_item_per_kind(object_layer_only=False)
    assert expected, "the table has no ABox row with individual positions?"
    assert _all_individuals(abox) == expected
    assert _all_individuals(abox) == dl_tableau._abox_individual_names(abox)
    assert owl_reasoner._all_individuals(abox) == expected
    assert set(dl.kb_to_fol(dl.TBox(), abox).individuals) == expected
    # an ABox that names nobody: nobody, on every route (the tableau's
    # abox_consistent alone invents the anonymous "a", and never reports it)
    empty = dl.ABox()
    assert (_all_individuals(empty) == owl_reasoner._all_individuals(empty)
            == dl_tableau._abox_individual_names(empty) == set())
    assert dl.kb_to_fol(dl.TBox(), empty).individuals == ()


def test_the_sweep_agrees_with_the_hermit_route_on_the_object_layer():
    from unicode_fol_kit.dl import owl_reasoner

    abox, expected = _abox_with_one_item_per_kind(object_layer_only=True)
    assert _all_individuals(abox) == owl_reasoner._all_individuals(abox) == expected


# =============================================================================
# [14] the TBox is rendered field by field too: every row of the axiom-kind
# table with holder "tbox" must reach the uploaded document.
# =============================================================================

#: For each ``TBox`` field: ``(the value ONE stored axiom takes, the one axiom
#: line the document must then carry)``. The line is derived by hand from the
#: renderer's naming rule, never read off its output: a role is ``:R<n>``, a data
#: property ``:P<n>``, a class ``:C<n>`` and a USER datatype ``:T<n>``, each
#: numbered in order of first appearance WITHIN the one axiom (the document holds
#: nothing else), and a built-in datatype (``xsd:integer``) keeps its own name.
#: E.g. a chain ``r o s ⊑ t`` names ``r`` and ``s`` inside the chain first, so
#: ``:R1 :R2``, then its super-role ``t`` as ``:R3``; ``DatatypeDefinition(D
#: xsd:integer)`` names the user datatype ``D`` as ``:T1``.
_STORED_TBOX_SHAPES = {
    "inclusions": ((A, A), "SubClassOf(:C1 :C1)"),
    "role_inclusions": (("r", "s"), "SubObjectPropertyOf(:R1 :R2)"),
    "transitive_roles": ("r", "TransitiveObjectProperty(:R1)"),
    "inverse_role_pairs": (("r", "s"), "InverseObjectProperties(:R1 :R2)"),
    "role_chains": ((("r", "s"), "t"),
                    "SubObjectPropertyOf(ObjectPropertyChain(:R1 :R2) :R3)"),
    "disjoint_role_pairs": (("r", "s"), "DisjointObjectProperties(:R1 :R2)"),
    "symmetric_roles": ("r", "SymmetricObjectProperty(:R1)"),
    "asymmetric_roles": ("r", "AsymmetricObjectProperty(:R1)"),
    "reflexive_roles": ("r", "ReflexiveObjectProperty(:R1)"),
    "irreflexive_roles": ("r", "IrreflexiveObjectProperty(:R1)"),
    "functional_roles": ("r", "FunctionalObjectProperty(:R1)"),
    "inverse_functional_roles": ("r", "InverseFunctionalObjectProperty(:R1)"),
    "role_domains": (("r", A), "ObjectPropertyDomain(:R1 :C1)"),
    "role_ranges": (("r", A), "ObjectPropertyRange(:R1 :C1)"),
    "data_property_inclusions": (("d", "e"), "SubDataPropertyOf(:P1 :P2)"),
    "disjoint_data_property_pairs": (("d", "e"), "DisjointDataProperties(:P1 :P2)"),
    "functional_data_properties": ("d", "FunctionalDataProperty(:P1)"),
    "data_property_domains": (("d", A), "DataPropertyDomain(:P1 :C1)"),
    "data_property_ranges": (("d", dl.Datatype("xsd:integer")),
                             "DataPropertyRange(:P1 xsd:integer)"),
    "datatype_definitions": (("D", dl.Datatype("xsd:integer")),
                             "DatatypeDefinition(:T1 xsd:integer)"),
}


def _tbox_rows():
    """One row per TBox FIELD of the axiom-kind table (two kinds may share a
    field: ``SubClassOf`` and ``EquivalentClasses`` both live in ``inclusions``)."""
    seen, rows = set(), []
    for row in dl_tableau._AXIOM_KINDS:
        if row.holder == "tbox" and row.field not in seen:
            seen.add(row.field)
            rows.append(row)
    return rows


def test_the_table_and_the_dataclass_name_the_same_tbox_fields():
    # a TBox field the table lacks is a field NO consumer derived from the table
    # knows about -- this document renderer included
    assert {row.field for row in _tbox_rows()} == {f.name for f in dataclasses.fields(dl.TBox)}


@pytest.mark.parametrize("row", _tbox_rows(), ids=lambda row: row.field)
def test_the_document_renders_exactly_one_axiom_for_every_tbox_field(row):
    """The renderer lists every ``TBox`` field by hand; a field added later and
    not rendered would reach the uploaded document as NOTHING, and FaCT++ would
    be asked about a strictly weaker knowledge base than the caller's. One
    stored axiom per field must come out as exactly one axiom line (a
    ``Declaration`` is not an axiom), and as the line derived above."""
    assert row.field in _STORED_TBOX_SHAPES, (
        f"TBox.{row.field} ({row.kind}) has no sample shape here: add a shape")
    stored, expected = _STORED_TBOX_SHAPES[row.field]
    tbox = dl.TBox()
    holder = getattr(tbox, row.field)
    (holder.add if isinstance(holder, set) else holder.append)(stored)
    body = [line.strip() for line in _render_document(tbox, dl.ABox()).splitlines()
            if line.startswith("  ")]
    axioms = [line for line in body if not line.startswith("Declaration(")]
    assert axioms == [expected], (row.field, body)
