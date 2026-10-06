r"""The HETS-route acceptance run against a real, local HETS output set.

Opt-in and skipped by default, following the convention the kit's five other
access-gated corpora already use (``UFK_FRACAS_XML``,
``UFK_PFOLIO_CSV``/``UFK_FOLIO_CSV``, ``UFK_PMB_SBN_DIR``, ``UFK_LEO3``,
``UFK_OEO_AXIOMS_JSONL``): ``UFK_*`` variables read at module level with the
``skipif`` marker in this module, no shared ``conftest.py`` (there is none).

FOUR variables, not ``tests/test_owl_corpus.py``'s one. That file's
``$UFK_OEO_AXIOMS_JSONL`` is a per-axiom JSONL for the ``dl`` route and has
nothing a HETS test can use; this package's oracle is HETS' own output, which
is four different artefacts:

``$UFK_OEO_DG_JSON``
    The raw ``GET /dg?format=json`` body for the FULL ontology, exactly as
    HETS sent it — 8,345,206 characters, invalid JSON.
``$UFK_OEO_TPTP``
    The ``-o tptp`` file from the LOSSY (``-Y``) run of the same full
    ontology — 1,367,212 bytes, 4291 ``fof``. Pairs with the dg body above:
    both are the full ontology, so the ``Ax<N>`` ↔ ``ax_ax<N>`` index
    correspondence holds.
``$UFK_OEO_THEORY_TPTP``
    The REST ``GET /theory?...&translation=OWL22CASL:CASL2TPTP_FOF`` body for
    the REDUCED ontology (the one with the two ``DataPropertyRange(d
    rdfs:Literal)`` axioms removed) — 1,554,903 characters, header included.
``$UFK_OEO_TPTP_REDUCED``
    The ``-o tptp`` file from the non-lossy run of that same REDUCED
    ontology — also 1,367,212 bytes.

The last two are a separate pair ON PURPOSE, and this is a correction to the
implementation spec, which said the stripped REST body is byte-identical to
"the 1,367,212-byte ``-o tptp`` file". Both CLI files are 1,367,212 bytes, but
they are not the same file: removing the two ``DataPropertyRange`` axioms
shifts every later ``Ax<N>`` index by one, so the full-lossy and reduced
outputs first differ at ``ax_ax4027`` (``ax_ax4027`` against ``ax_ax4028``).
The byte-identity holds for the REDUCED pair, and that is what is asserted
below.

None of these files is ever committed. They are 1.3-8.3 MB of another
project's HETS run; the kit holds tools, not corpora, and the committed suite
carries hand-written fixtures that reproduce each defect instead
(``tests/test_hets_haskell_json.py``, ``tests/test_hets_client_oeo.py``,
``tests/test_hets_symbols.py``, ``tests/test_tptp_parser_agreement.py``).

Every number asserted here was re-measured on this tree, not copied from the
request. The one slow assertion (the whole-file Earley/LALR identity run,
~70 s) is marked ``slow`` so it stays out of the everyday loop.
"""

import io
import json
import os
import time
from pathlib import Path

import pytest

from unicode_fol_kit.fol.tptp_input import (
    _FILE_PARSER,
    _TRANSFORMER,
    load_tptp_problem,
    parse_tptp,
)
from unicode_fol_kit.hets import (
    hets_prefixes,
    hets_symbol_table,
    repair_haskell_json,
    strip_hets_theory_header,
    untranslated_axioms,
)

_DG = os.environ.get("UFK_OEO_DG_JSON")
_TPTP = os.environ.get("UFK_OEO_TPTP")
_THEORY = os.environ.get("UFK_OEO_THEORY_TPTP")
_TPTP_REDUCED = os.environ.get("UFK_OEO_TPTP_REDUCED")

_REASON = (
    "set $UFK_OEO_DG_JSON (the raw GET /dg body for the full ontology), "
    "$UFK_OEO_TPTP (its lossy -o tptp file), $UFK_OEO_THEORY_TPTP (the REST "
    "/theory body for the REDUCED ontology) and $UFK_OEO_TPTP_REDUCED (that "
    "ontology's -o tptp file) to local copies of a HETS output set; these "
    "files are 1.3-8.3 MB and are never committed — the kit holds tools, not "
    "corpora")


def _have(*paths):
    return all(path and Path(path).is_file() for path in paths)


dg_and_tptp = pytest.mark.skipif(not _have(_DG, _TPTP), reason=_REASON)
theory_pair = pytest.mark.skipif(
    not _have(_THEORY, _TPTP_REDUCED), reason=_REASON)
tptp_only = pytest.mark.skipif(not _have(_TPTP), reason=_REASON)


def _read(path):
    # newline="" so a CR or CRLF in the file reaches the reader unchanged --
    # the byte-identity assertion below is meaningless otherwise.
    return io.open(path, encoding="utf-8", newline="").read()


# =============================================================================
# B3
# =============================================================================

@dg_and_tptp
def test_the_real_dg_body_is_repaired_and_loads():
    raw = _read(_DG)
    with pytest.raises(json.JSONDecodeError, match=r"Invalid \\escape"):
        json.loads(raw)

    started = time.monotonic()
    repair = repair_haskell_json(raw)
    elapsed = time.monotonic() - started
    assert repair.decimal_escapes == 897
    assert repair.decimal_runs == 389
    assert repair.empty_separators == 7
    assert repair.mnemonic_escapes == 0
    # A ceiling, generously above the 0.42 s measured, never an equality.
    assert elapsed < 5.0, f"repair took {elapsed:.2f}s"

    graph = json.loads(repair.text)["DGraph"]
    nodes = graph["DGNode"]
    assert len(nodes) == 1
    assert nodes[0]["name"] == "https://openenergyplatform.org/ontology/oeo/"
    axioms = nodes[0]["Axioms"]
    assert len(axioms) == 13032
    assert axioms[0]["name"] == "Ax1" and axioms[-1]["name"] == "Ax13032"
    declarations = nodes[0]["Declarations"]
    assert len(declarations) == 2099
    counts = {}
    for declaration in declarations:
        counts[declaration["kind"]] = counts.get(declaration["kind"], 0) + 1
    assert counts == {"Class": 1611, "Individual": 223, "ObjectProperty": 182,
                      "AnnotationProperty": 68, "DataProperty": 8,
                      "Datatype": 7}

    # The two witness characters: U+2019 from \226\128\153 and U+00A7 from
    # \194\167 (with the following \& removed, so the literal 7 survives).
    by_name = {axiom["name"]: axiom["Axiom"] for axiom in axioms}
    assert "Verdi’s Requiem" in by_name["Ax4035"]
    assert any("§7 Absatz 3 ROG" in text for text in by_name.values())


# =============================================================================
# B5 — the strongest assertion in this package: the REST route and the CLI
# route deliver the same text, so the two are interchangeable.
# =============================================================================

@theory_pair
def test_the_stripped_rest_theory_is_byte_identical_to_the_cli_file():
    theory = _read(_THEORY)
    header, body = strip_hets_theory_header(theory)
    assert len(theory) == 1554903
    assert len(header) == 187689
    assert header.startswith("logic TPTP.FOF")
    assert header.rstrip().endswith("}%")
    assert header.count("\n") + 1 == 2267
    assert len(body) == 1367214
    assert body.lstrip("\r\n") == _read(_TPTP_REDUCED)


@theory_pair
def test_the_stripped_rest_theory_parses_to_the_same_formula_count():
    _header, body = strip_hets_theory_header(_read(_THEORY))
    assert len(parse_tptp(body)) == 4291


# =============================================================================
# B6
# =============================================================================

@tptp_only
def test_the_whole_real_file_loads_fast_enough_to_be_usable():
    """68.3 s before, 1.7 s after. A CEILING, never an equality.

    The budget is deliberately far above the measured 1.7 s: a tight bound
    would fail on a loaded machine and teach whoever hits it to raise the
    number rather than look. What it must catch is the fast path silently
    falling back to Earley for every parse, which costs 40x.
    """
    started = time.monotonic()
    problem = load_tptp_problem(_TPTP)
    elapsed = time.monotonic() - started
    assert len(problem.formulas) == 4291
    assert all(formula.role == "axiom" for formula in problem.formulas)
    assert elapsed < 15.0, f"load_tptp_problem took {elapsed:.1f}s"


@tptp_only
@pytest.mark.skipif(
    not os.environ.get("UFK_OEO_PARSER_IDENTITY"),
    reason="set $UFK_OEO_PARSER_IDENTITY=1 to also run the whole-file "
           "Earley/LALR identity check; it costs the full Earley parse "
           "(~70 s) and so is kept out of the everyday loop. A separate "
           "variable rather than a `slow` marker, because registering a new "
           "marker means editing pyproject.toml, which this package does not "
           "own")
def test_both_parsers_produce_identical_asts_for_all_4291_formulas():
    """The identity claim, over the whole file rather than a sample.

    It is the assertion the agreement battery in
    tests/test_tptp_parser_agreement.py scales up: 46 hand-written probes
    plus this.
    """
    fast = load_tptp_problem(_TPTP)
    slow_items = _TRANSFORMER.transform(_FILE_PARSER.parse(_read(_TPTP)))
    assert len(slow_items) == 4291
    assert list(fast.formulas) == slow_items
    assert fast.header == load_tptp_problem(_TPTP).header


# =============================================================================
# C1
# =============================================================================

@dg_and_tptp
def test_the_real_symbol_table_joins_2026_of_2099_declarations():
    dg = json.loads(repair_haskell_json(_read(_DG)).text)
    tptp = _read(_TPTP)
    table = hets_symbol_table(dg, tptp)
    assert len(table.symbols) == 2099
    assert sum(1 for s in table.symbols if s.in_tptp) == 2026
    missing = [s for s in table.symbols if not s.in_tptp]
    assert len(missing) == 73
    kinds = {}
    for symbol in missing:
        kinds[symbol.kind] = kinds.get(symbol.kind, 0) + 1
    # 68 annotation properties (no logical content under OWL 2's direct
    # semantics) + 5 object properties declared but used in no axiom.
    assert kinds == {"AnnotationProperty": 68, "ObjectProperty": 5}

    assert table.unmapped_tptp == (
        "op_0", "op_1", "op_2", "op_3", "op_4", "op_5", "op_6", "op_7",
        "op_8", "op_9", "op___U40U40__", "pred_Nothing", "pred_Thing",
        "pred_____", "sort_DATA", "sort_Thing",
        "sort_http_u_u_uwww_uw3_uorg_u2001_uXMLSchema_uinteger",
        "sort_xsd_udateTime", "sort_xsd_udecimal", "sort_xsd_uinteger",
        "sort_xsd_ustring")

    rows = sum(len(symbol.labels) for symbol in table.symbols)
    assert rows == 1685
    tags = {}
    for symbol in table.symbols:
        for _label, lang in symbol.labels:
            tags[lang] = tags.get(lang, 0) + 1
    assert tags == {"en": 1666, "": 18, "de": 1}

    found = table.by_label("biofuel")
    assert len(found) == 1
    assert found[0].iri.endswith("OEO_00000072")
    assert found[0].tptp_name == (
        "pred_https_u_u_uopenenergyplatform_uorg_uontology_uoeo_u"
        "OEO_00000072")


@dg_and_tptp
def test_an_absent_prefix_map_is_reported_rather_than_silently_degrading():
    """432 of the 2099 declarations are CURIEs, over 10 distinct prefixes.

    Without a prefix map their ``iri`` is still a CURIE, which cannot be
    joined with the OWL file or with the ``dl`` route — so the table says
    which prefixes it could not expand instead of leaving the caller to
    notice. This is the defect the live run surfaced: the TRANSLATED ``.th``
    of a TPTP chain carries zero ``Prefix:`` lines (the source rendering
    ``pp.dol`` carries all 15), so reading them from the wrong output left
    every one of the 432 unexpanded with nothing saying so.
    """
    dg = json.loads(repair_haskell_json(_read(_DG)).text)
    tptp = _read(_TPTP)

    bare = hets_symbol_table(dg, tptp)
    curies = [s for s in bare.symbols if ":" in s.printed
              and "://" not in s.printed]
    assert len(curies) == 432
    assert set(bare.unexpanded_prefixes) == {
        "dc", "foaf", "obo", "oboInOwl", "owl", "prov", "rdfs", "skos",
        "terms", "www"}

    prefixes = {
        "obo": "http://purl.obolibrary.org/obo/",
        "rdfs": "http://www.w3.org/2000/01/rdf-schema#",
        "owl": "http://www.w3.org/2002/07/owl#",
        "skos": "http://www.w3.org/2004/02/skos/core#",
        "dc": "http://purl.org/dc/elements/1.1/",
        "terms": "http://purl.org/dc/terms/",
        "oboInOwl": "http://www.geneontology.org/formats/oboInOwl#",
        "prov": "http://www.w3.org/ns/prov#",
        "foaf": "http://xmlns.com/foaf/0.1/",
        "www": "https://www.commoncoreontologies.org/",
    }
    table = hets_symbol_table(dg, tptp, prefixes=prefixes)
    assert table.unexpanded_prefixes == ()
    assert all(s.iri.startswith(("http://", "https://")) for s in table.symbols)
    row = table.by_printed("obo:BFO_0000001")
    assert row.iri == "http://purl.obolibrary.org/obo/BFO_0000001"
    assert row.tptp_name == "pred_obo_uBFO_0000001"


@dg_and_tptp
def test_exactly_two_logical_axioms_have_no_tptp_image():
    """The -Y loss, derived from the Ax<N> <-> ax_ax<N> name correspondence.

    The requesting project reached the same two axioms by diffing against a
    hand-reduced ontology — a completely different method. Two independent
    derivations agreeing is what makes the 2 trustworthy.
    """
    dg = json.loads(repair_haskell_json(_read(_DG)).text)
    tptp = _read(_TPTP)
    omitted = untranslated_axioms(dg, tptp)
    assert [axiom.name for axiom in omitted] == ["Ax4027", "Ax4030"]
    assert all(axiom.kind == "DataPropertyRange" for axiom in omitted)
    assert omitted[0].owl == (
        "DataPropertyRange( https://openenergyplatform.org/ontology/oeo/"
        "OEO_00390094 rdfs:Literal )")
    assert omitted[1].owl == (
        "DataPropertyRange( https://openenergyplatform.org/ontology/oeo/"
        "OEO_00390098 rdfs:Literal )")

    everything = untranslated_axioms(dg, tptp, include_annotations=True)
    assert len(everything) == 8997
    kinds = {}
    for axiom in everything:
        kinds[axiom.kind] = kinds.get(axiom.kind, 0) + 1
    assert kinds == {"AnnotationAssertion": 8991,
                     "SubAnnotationPropertyOf": 4,
                     "DataPropertyRange": 2}
