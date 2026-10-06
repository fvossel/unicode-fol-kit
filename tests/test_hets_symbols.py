r"""C1 (pure half): joining HETS' TPTP symbols back onto OWL entities.

Offline throughout — ``hets_symbol_table``, ``untranslated_axioms`` and
``hets_prefixes`` are pure functions over a ``/dg`` dict and a TPTP string, so
nothing here needs a server. The ``/dg`` fixture below is a hand-written dict
literal in the real response's shape (``{kind, name, iri, Symbol}`` per
declaration, ``{name, Axiom, SenSymbols}`` per axiom), and the TPTP fixture is
eight hand-written lines; the real pair is 8.3 MB + 1.37 MB and is never
committed.

The mangling expectations are DERIVED from the rule, not copied from the
code's output: replace every character outside ``[A-Za-z0-9_]`` with ``_u``,
then prefix ``op_`` for an Individual, ``sort_`` for a Datatype and ``pred_``
for everything else. So ``obo:BFO_0000001`` (Class) becomes
``pred_obo_uBFO_0000001`` — one ``:`` replaced — and
``https://openenergyplatform.org/ontology/oeo/OEO_00000072`` becomes
``pred_https_u_u_uopenenergyplatform_uorg_uontology_uoeo_uOEO_00000072`` —
the ``:`` and each of the six ``/`` and two ``.`` replaced, which is exactly
the string the OEO request quotes.
"""

import pytest

from unicode_fol_kit.hets import (
    HetsSymbolCollisionError,
    UntranslatedAxiom,
    hets_prefixes,
    hets_symbol_table,
    untranslated_axioms,
)

OBO = "http://purl.obolibrary.org/obo/"
OEO = "https://openenergyplatform.org/ontology/oeo/"

DG = {
    "DGraph": {
        "libname": OEO,
        "DGNode": [{
            "name": OEO,
            "logic": "OWL",
            "Declarations": [
                {"kind": "Class", "name": "BFO_0000001",
                 "iri": "obo:BFO_0000001",
                 "Symbol": "Class obo:BFO_0000001"},
                {"kind": "Class", "name": OEO + "OEO_00000072",
                 "iri": OEO + "OEO_00000072",
                 "Symbol": "Class " + OEO + "OEO_00000072"},
                {"kind": "Individual", "name": OEO + "OEO_00000099",
                 "iri": OEO + "OEO_00000099",
                 "Symbol": "Individual " + OEO + "OEO_00000099"},
                {"kind": "Datatype", "name": "xsd:integer",
                 "iri": "xsd:integer", "Symbol": "Datatype xsd:integer"},
                {"kind": "AnnotationProperty", "name": "IAO_0000112",
                 "iri": "obo:IAO_0000112",
                 "Symbol": "AnnotationProperty obo:IAO_0000112"},
                {"kind": "ObjectProperty", "name": "BFO_0000050",
                 "iri": "obo:BFO_0000050",
                 "Symbol": "ObjectProperty obo:BFO_0000050"},
            ],
            "Axioms": [
                {"name": "Ax1",
                 "Axiom": "SubClassOf( " + OEO + "OEO_00000072 "
                          "obo:BFO_0000001 )"},
                {"name": "Ax2",
                 "Axiom": 'AnnotationAssertion( rdfs:label obo:BFO_0000001 '
                          '"entity"@en )'},
                {"name": "Ax3",
                 "Axiom": 'AnnotationAssertion( rdfs:label '
                          + OEO + 'OEO_00000072 "biofuel"@en )'},
                {"name": "Ax4",
                 "Axiom": "DataPropertyRange( " + OEO + "OEO_00390094 "
                          "rdfs:Literal )"},
            ],
        }],
    },
}

# Eight lines mentioning only Ax1's symbols, plus three symbols with no
# declaration behind them (a CASL numeral, an OWL built-in and a HETS sort).
TPTP = """fof(ax_ax1, axiom,
    ! [VAR_X]:
    ((pred_https_u_u_uopenenergyplatform_uorg_uontology_uoeo_uOEO_00000072(VAR_X))
     => pred_obo_uBFO_0000001(VAR_X))).

fof(sign_non_empty_sort_DATA, axiom, ? [VAR_Y]: sort_DATA(VAR_Y)).
fof(ax_thing_in_thing, axiom, ! [VAR_X]: pred_Thing(VAR_X)).
fof(extra, axiom, p(op_1, op_https_u_u_uopenenergyplatform_uorg_uontology_uoeo_uOEO_00000099, sort_xsd_uinteger)).
"""

PREFIXES = {"obo": OBO, "xsd": "http://www.w3.org/2001/XMLSchema#", "": OEO}


@pytest.fixture
def table():
    return hets_symbol_table(DG, TPTP, prefixes=PREFIXES)


def test_a_curie_declaration_is_expanded_and_mangled(table):
    row = table.by_printed("obo:BFO_0000001")
    assert row.printed == "obo:BFO_0000001"
    assert row.iri == OBO + "BFO_0000001"
    assert row.name == "BFO_0000001"
    assert row.kind == "Class"
    assert row.tptp_name == "pred_obo_uBFO_0000001"
    assert row.kit_name == "Pred_obo_uBFO_0000001"
    assert row.in_tptp is True


def test_a_full_iri_declaration_mangles_to_the_string_the_request_quotes(table):
    row = table.by_iri(OEO + "OEO_00000072")
    assert row.tptp_name == (
        "pred_https_u_u_uopenenergyplatform_uorg_uontology_uoeo_u"
        "OEO_00000072")
    assert row.kit_name == (
        "Pred_https_u_u_uopenenergyplatform_uorg_uontology_uoeo_u"
        "OEO_00000072")
    assert row.in_tptp is True


def test_an_individual_gets_op_and_a_datatype_gets_sort(table):
    individual = table.by_iri(OEO + "OEO_00000099")
    assert individual.kind == "Individual"
    assert individual.tptp_name.startswith("op_")
    assert individual.in_tptp is True

    datatype = table.by_printed("xsd:integer")
    assert datatype.kind == "Datatype"
    assert datatype.tptp_name == "sort_xsd_uinteger"
    assert datatype.iri == "http://www.w3.org/2001/XMLSchema#integer"
    assert datatype.in_tptp is True


def test_a_declaration_with_no_symbol_in_the_tptp_is_a_reported_fact(table):
    """68 AnnotationProperty + 5 unused ObjectProperty on the real ontology.

    An annotation property carries no logical content under OWL 2's direct
    semantics, so a comorphism legitimately never emits it; an object
    property used in no logical axiom simply does not occur. Both are rows
    with ``in_tptp=False``, never dropped and never an error.
    """
    annotation = table.by_printed("obo:IAO_0000112")
    assert annotation.kind == "AnnotationProperty"
    assert annotation.in_tptp is False
    unused = table.by_printed("obo:BFO_0000050")
    assert unused.kind == "ObjectProperty"
    assert unused.tptp_name == "pred_obo_uBFO_0000050"
    assert unused.in_tptp is False
    assert len(table.symbols) == 6          # all six rows kept


def test_tptp_symbols_with_no_declaration_are_reported(table):
    """A formula over one of these is a formula the table cannot explain."""
    assert table.unmapped_tptp == ("op_1", "pred_Thing", "sort_DATA")


def test_every_lookup_index_is_built_from_the_forward_map(table):
    row = table.by_printed("obo:BFO_0000001")
    assert table.by_tptp_name(row.tptp_name) is row
    assert table.by_kit_name(row.kit_name) is row
    assert table.by_iri(row.iri) is row
    assert table.by_printed("nope") is None
    assert table.by_tptp_name("pred_nope") is None


def test_labels_are_collected_with_their_language_tag(table):
    assert table.by_printed("obo:BFO_0000001").labels == (("entity", "en"),)
    assert table.by_iri(OEO + "OEO_00000072").labels == (("biofuel", "en"),)
    # No label for the datatype, and that is a tuple, not None.
    assert table.by_printed("xsd:integer").labels == ()


def test_by_label_returns_a_tuple_even_for_a_unique_label(table):
    found = table.by_label("entity")
    assert len(found) == 1
    assert found[0].iri == OBO + "BFO_0000001"
    assert table.by_label("entity", lang="de") == ()
    assert table.by_label("no such label") == ()


def test_by_label_returns_both_subjects_when_a_label_is_shared():
    """rdfs:label is not required to be unique in OWL 2.

    No OEO label is shared by two subjects, so the plural return type would
    otherwise never be exercised — and a function that returned ONE symbol
    would silently pick for the caller on the next ontology.
    """
    shared = {"DGraph": {"DGNode": [{
        "name": "n",
        "Declarations": [
            {"kind": "Class", "name": "A", "iri": ":A"},
            {"kind": "Class", "name": "B", "iri": ":B"},
        ],
        "Axioms": [
            {"name": "Ax1",
             "Axiom": 'AnnotationAssertion( rdfs:label :A "thing"@en )'},
            {"name": "Ax2",
             "Axiom": 'AnnotationAssertion( rdfs:label :B "thing"@en )'},
        ],
    }]}}
    table = hets_symbol_table(shared, "")
    found = table.by_label("thing")
    assert sorted(symbol.printed for symbol in found) == [":A", ":B"]


def test_an_untagged_label_is_reachable_with_lang_empty():
    """18 of OEO's 1685 labels carry no language tag."""
    dg = {"DGraph": {"DGNode": [{
        "name": "n",
        "Declarations": [{"kind": "Class", "name": "A", "iri": ":A"}],
        "Axioms": [{"name": "Ax1",
                    "Axiom": 'AnnotationAssertion( rdfs:label :A "bare" )'}],
    }]}}
    table = hets_symbol_table(dg, "")
    assert table.by_printed(":A").labels == (("bare", ""),)
    assert table.by_label("bare", lang="") == (table.symbols[0],)
    assert table.by_label("bare") == ()          # not tagged @en


def test_two_printed_forms_that_mangle_alike_refuse_to_build():
    r"""``a:b`` and ``a/b`` both mangle to ``pred_a_ub``.

    HETS' mangling is not injective, so this is possible in principle (it
    does not occur in OEO). Keeping whichever declaration came last would
    make every later lookup for the other entity answer about the wrong one.
    """
    clashing = {"DGraph": {"DGNode": [{
        "name": "n",
        "Declarations": [
            {"kind": "Class", "name": "b", "iri": "a:b"},
            {"kind": "Class", "name": "b", "iri": "a/b"},
        ],
        "Axioms": [],
    }]}}
    with pytest.raises(HetsSymbolCollisionError) as caught:
        hets_symbol_table(clashing, "")
    message = str(caught.value)
    assert "pred_a_ub" in message
    assert "a:b" in message and "a/b" in message


def test_without_a_prefix_map_the_iri_is_the_printed_form():
    table = hets_symbol_table(DG, TPTP)
    row = table.by_printed("obo:BFO_0000001")
    assert row.iri == "obo:BFO_0000001"
    # ... and a full IRI is still never mistaken for a CURIE.
    assert table.by_printed(OEO + "OEO_00000072").iri == OEO + "OEO_00000072"


def test_a_curie_that_could_not_be_expanded_is_reported_not_hidden():
    """An absent prefix map must not degrade the table silently.

    A CURIE cannot be joined with the OWL file or with the `dl` route, so a
    row whose `iri` is still `obo:BFO_0000001` is a row that will not match
    anything -- and this field is how a caller finds out, the same way
    `unmapped_tptp` reports the other direction. Found by running the real
    ontology through `owl_to_tptp`: the TRANSLATED `.th` of a TPTP chain
    carries zero `Prefix:` lines, so the prefix map came back empty and all
    432 CURIE declarations stayed CURIEs with nothing saying so.
    """
    assert hets_symbol_table(DG, TPTP).unexpanded_prefixes == ("obo", "xsd")
    # With the map, nothing is left over.
    assert hets_symbol_table(DG, TPTP, prefixes=PREFIXES).unexpanded_prefixes == ()
    # A partial map reports exactly what is still missing.
    partial = hets_symbol_table(DG, TPTP, prefixes={"obo": OBO})
    assert partial.unexpanded_prefixes == ("xsd",)
    assert partial.by_printed("obo:BFO_0000001").iri == OBO + "BFO_0000001"
    assert partial.by_printed("xsd:integer").iri == "xsd:integer"


def test_an_ambiguous_node_is_refused_rather_than_picked():
    two = {"DGraph": {"DGNode": [
        {"name": "a", "Declarations": [], "Axioms": []},
        {"name": "b", "Declarations": [], "Axioms": []},
    ]}}
    with pytest.raises(ValueError, match="pass node="):
        hets_symbol_table(two, "")
    assert hets_symbol_table(two, "", node="b").symbols == ()
    with pytest.raises(ValueError, match="no development-graph node named"):
        hets_symbol_table(two, "", node="c")


def test_an_empty_graph_is_refused_by_name():
    with pytest.raises(ValueError, match="has no DGNode"):
        hets_symbol_table({"DGraph": {"DGNode": None}}, "")


# =============================================================================
# untranslated_axioms
# =============================================================================

def test_only_the_non_annotation_axiom_is_reported_as_omitted():
    """Ax4 has no ax_ax4 formula; Ax2/Ax3 are annotation axioms.

    The exclusion is an OWL 2 SPEC fact: the direct semantics gives
    AnnotationAssertion no consequence, so a comorphism that drops it loses
    nothing. On the real pair this same rule picks out exactly the two
    DataPropertyRange axioms the lossy run drops, agreeing with the
    requesting project's own count reached by a different method.
    """
    omitted = untranslated_axioms(DG, TPTP)
    assert omitted == (UntranslatedAxiom(
        name="Ax4",
        owl="DataPropertyRange( " + OEO + "OEO_00390094 rdfs:Literal )",
        kind="DataPropertyRange"),)


def test_include_annotations_reports_the_annotation_axioms_too():
    omitted = untranslated_axioms(DG, TPTP, include_annotations=True)
    assert [a.name for a in omitted] == ["Ax2", "Ax3", "Ax4"]
    assert [a.kind for a in omitted] == [
        "AnnotationAssertion", "AnnotationAssertion", "DataPropertyRange"]


def test_an_axiom_with_a_formula_is_never_reported():
    assert all(a.name != "Ax1" for a in
               untranslated_axioms(DG, TPTP, include_annotations=True))


def test_duplicate_formula_names_do_not_make_an_axiom_look_missing():
    """19 ax_ax<N> names are duplicated in the real file — a HETS defect.

    The comparison is between SETS of indices, so a duplicate cannot change
    the answer and cannot crash.
    """
    doubled = TPTP + "\nfof(ax_ax1, axiom, pred_obo_uBFO_0000001(c)).\n"
    assert untranslated_axioms(DG, doubled) == untranslated_axioms(DG, TPTP)
    assert all(a.name != "Ax1" for a in
               untranslated_axioms(DG, doubled, include_annotations=True))


def test_nothing_omitted_is_an_empty_tuple_not_none():
    """() means 'computed, and the answer is none'; None means 'not computed'."""
    complete = {"DGraph": {"DGNode": [{
        "name": "n", "Declarations": [],
        "Axioms": [{"name": "Ax1", "Axiom": "SubClassOf( :A :B )"}],
    }]}}
    assert untranslated_axioms(complete, "fof(ax_ax1, axiom, p).") == ()


# =============================================================================
# hets_prefixes
# =============================================================================

# The real 15-line Prefix block of oeo-hets.pp.dol, verbatim.
PP_DOL_HEAD = """library https://openenergyplatform.org/ontology/oeo/

logic OWL

spec https://openenergyplatform.org/ontology/oeo/ =
     Prefix: : <https://openenergyplatform.org/ontology/oeo/>
     Prefix: dc: <http://purl.org/dc/elements/1.1/>
     Prefix: foaf: <http://xmlns.com/foaf/0.1/>
     Prefix: obo: <http://purl.obolibrary.org/obo/>
     Prefix: oboInOwl: <http://www.geneontology.org/formats/oboInOwl#>
     Prefix: oeo: <https://openenergyplatform.org/ontology/oeo/>
     Prefix: owl: <http://www.w3.org/2002/07/owl#>
     Prefix: prov: <http://www.w3.org/ns/prov#>
     Prefix: rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
     Prefix: rdfs: <http://www.w3.org/2000/01/rdf-schema#>
     Prefix: skos: <http://www.w3.org/2004/02/skos/core#>
     Prefix: terms: <http://purl.org/dc/terms/>
     Prefix: www: <https://www.commoncoreontologies.org/>
     Prefix: xml: <http://www.w3.org/XML/1998/namespace>
     Prefix: xsd: <http://www.w3.org/2001/XMLSchema#>

     Ontology: <https://openenergyplatform.org/ontology/oeo/>
"""


def test_the_prefix_block_is_read_including_the_empty_prefix():
    prefixes = hets_prefixes(PP_DOL_HEAD)
    assert len(prefixes) == 15
    assert prefixes[""] == OEO
    assert prefixes["obo"] == OBO
    assert prefixes["xsd"] == "http://www.w3.org/2001/XMLSchema#"
    # The `library`/`spec`/`Ontology:` lines are not prefixes.
    assert "library" not in prefixes


def test_a_text_with_no_prefix_block_gives_an_empty_map():
    assert hets_prefixes("fof(a, axiom, p).") == {}


def test_a_repeated_prefix_keeps_the_last_binding():
    """What a reader of the document would see."""
    assert hets_prefixes(
        "Prefix: p: <http://a/>\nPrefix: p: <http://b/>") == {"p": "http://b/"}
