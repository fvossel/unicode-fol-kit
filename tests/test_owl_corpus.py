r"""The OWL corpus harness: how much of a real ontology this kit can take.

Opt-in and skipped by default. The kit holds tools, not corpora, so the Open
Energy Ontology is never committed; point ``$UFK_OEO_AXIOMS_JSONL`` at a local
per-axiom record file and these tests run against it, following the convention
the kit's four other access-gated corpora already use (``UFK_FRACAS_XML``,
``UFK_PFOLIO_CSV``/``UFK_FOLIO_CSV``, ``UFK_PMB_SBN_DIR``, ``UFK_LEO3``): one
``UFK_*`` variable, read at module level, with the ``skipif`` marker in this
module rather than in a shared conftest.

The record file is JSON Lines, one object per axiom. Only three fields are
read: ``owlfs`` (the axiom's OWL 2 Functional-Style Syntax text — the INPUT),
and ``needs``/``kind`` (census keys). The records also carry a ``fol`` field;
it is deliberately NOT used as a gold image, because the copy this harness was
written against was measured on 0.28.1 and carries the pre-0.30.0 ``x_1``
variable shape. Expected images belong in a test file, hand-derived — see
``tests/test_owl_constructs_fixture.py``, which is the committed stand-in that
covers every construct in the default suite.

Why a JSONL of axioms rather than the ``.owl`` file: OEO ships as RDF/XML and
this kit has no RDF reader, so there is nothing a test could do with it. The
per-axiom record file is the only artefact the kit can consume, and it is also
where the ``needs`` census keys live — which is what makes a per-construct
floor possible instead of one opaque total.

What is asserted is a FLOOR per construct family, never an exact total: an OEO
point release shifts the counts, and a test that breaks on someone else's
release is a test nobody keeps. The breakdown is PRINTED (run with ``-s``), so
the next package can watch its own number move.

Deliberately NOT here: the tableau. Pushing 3091 GCIs through
``concept_satisfiable`` is a benchmark, not a test; the route agreement is
checked on hand-built knowledge bases in ``tests/test_dl_route_agreement.py``.
"""

import collections
import io
import json
import os
import re
from pathlib import Path

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.atp import generate_tptp_problem_with_mapping
from unicode_logic_kit.fol import Constant, is_bare_constant
from unicode_logic_kit.fol.sanitize import sanitize_names
from unicode_logic_kit.atp.tstp_check import _formula_alpha_equal

_REAL_OEO = os.environ.get("UFK_OEO_AXIOMS_JSONL")
real_corpus = pytest.mark.skipif(
    not (_REAL_OEO and Path(_REAL_OEO).is_file()),
    reason="set $UFK_OEO_AXIOMS_JSONL to a local OEO per-axiom record file "
           "(JSON Lines, one object per axiom, field 'owlfs' = the axiom's OWL "
           "functional syntax, 'needs'/'kind' = census keys); the corpus itself "
           "is never committed — the kit holds tools, not corpora")

# The ceiling on REFUSALS per construct family, measured on OEO 2.13.0 (4041
# axioms) with 0.30.0 and again after the data layer — equivalently, the floor
# on acceptance, which is what this harness exists to raise. Each number is how many axioms whose `needs`
# field names that construct are still refused today, so the package that
# implements the construct drives its entry to 0 and nothing else moves. A
# CEILING rather than an exact total so that a later OEO release adding axioms
# of an already-supported kind does not break the suite; a release adding
# axioms of a REFUSED kind does, which is the right way round — that is new
# work, not a passing test.
#
# `TopObjectProperty` is the odd one, and it is worth recording WHY it does not
# move with the role box. The kit now consumes a tautological inclusion into an
# OWL 2 built-in property as a documented no-op, in both W3C spellings
# (`owl:topObjectProperty` and the full `http://www.w3.org/2002/07/owl#...`
# IRI) -- and the full IRI is what oeo-full.owl itself carries, 36 times. But
# this record file's own `owlfs` text has already replaced that IRI with the
# requesting project's CamelCase SYMBOL, `TopObjectProperty`, which is not an
# OWL built-in spelling at all: so feeding this text to the kit legitimately
# builds an inclusion into an ordinary role of that name, and the 31 axioms
# stay "accepted" exactly as before. That is a lossiness in the record file,
# not in the kit; a harness that wants to observe the no-op must feed the
# built-in's real IRI. The reading itself is pinned by hand in
# tests/test_owl_constructs_fixture.py and tests/test_owl_functional.py.
#
# A ceiling of 0 means the construct is fully supported: the entry stays, so a
# later OEO release re-introducing an axiom the kit has stopped reading fails
# here rather than passing quietly.
_REFUSAL_CEILINGS = {
    "ObjectPropertyDomain": 0,              # value/domain/range: was 110
    "ObjectPropertyRange": 0,               # value/domain/range: was 108
    "ObjectHasValue": 0,                    # value/domain/range: was 95
    "TopObjectProperty": 1,
    "InverseObjectProperties": 0,          # the role box: was 27
    "DisjointObjectProperties": 0,         # the role box: was 17
    "DataPropertyDomain": 0,                # the data layer: was 7
    "DataRange": 0,                         # the data layer: was 7
    "DatatypeDefinition": 0,                # the data layer: was 7
    "SameIndividual": 0,                    # value/domain/range: was 7
    "ObjectPropertyChain": 0,              # the role box: was 5
    "DataPropertyRange": 0,                 # the data layer: was 5
    "DataHasValue": 0,                      # the data layer: was 4
    "SubAnnotationPropertyOf": 0,           # consumed and reported: was 4
    "DataPropertyAssertion": 0,             # the data layer: was 2
    "DataSomeValuesFrom": 0,                # the data layer: was 2
    "SymmetricObjectProperty": 0,          # the role box: was 1
    "AsymmetricObjectProperty": 0,         # the role box: was 1
    "IrreflexiveObjectProperty": 0,        # the role box: was 1
    "SubDataPropertyOf": 0,                 # the data layer: was 1
    "NegativeObjectPropertyAssertion": 0,   # value/domain/range: was 1
}

# Measured on this tree: 4041 of 4041 axioms parse and none is refused -- up
# from 4009 before the data layer, by exactly the 32 it accounts for (28 of the
# data layer proper: 7 DataPropertyDomain, 5 DataPropertyRange, 7
# DatatypeDefinition, 4 DataHasValue, 2 DataPropertyAssertion, 2
# DataSomeValuesFrom, 1 SubDataPropertyOf; plus the 4 SubAnnotationPropertyOf,
# which are now CONSUMED -- read, built into nothing, and reported by
# dl.parse_owl_functional_axioms in `consumed`). That in turn was up from 3688
# after the role box by the 321 axioms the value, domain/range and identity
# families account for, and from 3636 before the role box by its own 52. So the
# whole of OEO 2.13.0 is read. A floor, so the number can only be driven up.
_ACCEPTED_FLOOR = 4041
_TOTAL_FLOOR = 4041


def _records():
    for line in io.open(_REAL_OEO, encoding="utf-8"):
        line = line.strip()
        if line:
            yield json.loads(line)


def _needs(record):
    """The record's census keys as a list — ``needs`` may be absent, a string
    or a list, and an axiom the kit already takes has none.
    """
    needs = record.get("needs") or []
    return [needs] if isinstance(needs, str) else list(needs)


def _construct(message: str) -> str:
    """The construct phrase out of a refusal message, for the census.

    The refusals are built to NAME the construct — ``"... <phrase> is not
    supported — outside ALCHQ ..."`` — so grouping by that phrase is grouping
    by exactly what the kit says it cannot do. A message that does not name a
    construct is itself a finding, and shows up in the census as ``"?"``.
    """
    match = re.search(r"parse_owl_functional: (.+?) (?:is not supported|—)", message)
    return match.group(1) if match else "?"


def _print_census(title: str, counter: collections.Counter, total: int) -> None:
    print(f"\n{title} ({total} axioms)")
    for key, count in counter.most_common():
        print(f"  {count:5d}  {key}")


@real_corpus
def test_the_whole_oeo_corpus_translates():
    """How many of the corpus's axioms the kit takes, broken down by the
    construct each refusal names and by the ``needs`` field. The breakdown is
    printed so the next package can see its own number move.
    """
    records = list(_records())
    assert len(records) >= _TOTAL_FLOOR, (
        f"{len(records)} records; expected at least {_TOTAL_FLOOR}")
    accepted, refused = 0, collections.Counter()
    still_needed = collections.Counter()
    for record in records:
        try:
            dl.parse_owl_functional(f"Ontology({record['owlfs']})")
        except dl.OwlFunctionalSyntaxError as exc:
            refused[_construct(str(exc))] += 1
            for need in _needs(record) or ["<unlabelled>"]:
                still_needed[need] += 1
        else:
            accepted += 1
    _print_census("OEO axioms accepted by dl.parse_owl_functional", refused,
                  len(records))
    print(f"  accepted: {accepted} / {len(records)}")
    _print_census("still refused, by the construct the record says it needs",
                  still_needed, sum(still_needed.values()))

    assert accepted >= _ACCEPTED_FLOOR, (
        f"only {accepted} axioms parse; the floor is {_ACCEPTED_FLOOR}. This "
        "harness exists to move that number UP.")
    assert "?" not in refused, (
        "a refusal that does not name its construct: every refusal must say "
        "what it refused and what to use instead")
    for need, ceiling in _REFUSAL_CEILINGS.items():
        hit = still_needed.get(need, 0)
        assert hit <= ceiling, (
            f"{need}: {hit} axioms still refused, up from the measured "
            f"{ceiling} — a regression, not progress")


@real_corpus
def test_the_needs_census_accounts_for_every_refusal():
    """Every refused axiom is labelled with the construct it needs, and every
    label is one this package's spec knows about. An unlabelled refusal is a
    construct nobody has planned for.
    """
    labels = collections.Counter()
    for record in _records():
        try:
            dl.parse_owl_functional(f"Ontology({record['owlfs']})")
        except dl.OwlFunctionalSyntaxError:
            for need in _needs(record) or ["<unlabelled>"]:
                labels[need] += 1
    assert "<unlabelled>" not in labels, (
        "a refused axiom with no 'needs' label; the record file and this "
        "harness disagree about what the kit cannot read")
    assert set(labels) <= set(_REFUSAL_CEILINGS), (
        "construct families nobody planned for: "
        f"{sorted(set(labels) - set(_REFUSAL_CEILINGS))}")


def _names_a_quoted_individual(node) -> bool:
    """Does ``node`` carry a constant that its text writes in quotes?

    In OEO every individual is CamelCase, and a bare ``Gaseous`` would read as a
    predicate, so the text writes the constant ``'Gaseous'``. The scan counts
    these images to show that the quoted form is exercised at the scale of the
    corpus; a lower-case individual is written bare and is not counted.
    """
    return any(isinstance(sub, Constant) and not is_bare_constant(sub.name)
               for sub in node.walk())


def _names_a_prefixed_datatype(node) -> bool:
    """Does ``node`` carry a predicate named like ``xsd:integer`` (a built-in
    datatype by its prefixed name) -- the one name in the data image that is
    OWL's, not the kit's, and is not legal text in this grammar?"""
    return any(isinstance(getattr(sub, "predicate", None), str)
               and sub.predicate.split(":")[0] in ("xsd", "rdf", "rdfs", "owl")
               and ":" in sub.predicate
               for sub in node.walk())


@real_corpus
def test_no_printed_image_of_the_corpus_is_unreadable():
    """Everything the kit prints must read back, at the scale of a real
    ontology.

    An individual the ontology supplies is the caller's name, not one the
    translation minted, and in OEO every individual is CamelCase. Until 0.30.0
    such a constant printed as itself and re-read as a predicate term, so the
    axioms that name one were left out of this scan (711 of them). A constant
    whose bare name would read as something else is written in quotes now
    (``'Gaseous'``), so those axioms are in the scan like every other, and the
    count of images with a quoted individual is asserted to be large: a scan
    that met none would not be testing the quoted form.

    The constants are read off the IMAGE, not off ``kb.individuals``: that
    field is the ABox scan and is documented as such, and a caller's
    individual also reaches the TBox half — the ``ObjectHasValue(r a)`` image
    is ``∀x (C(x) → r(x, 'a'))`` and the ``ObjectOneOf(a)`` one
    ``∀x (C(x) → x = 'a')``, each with ``kb.individuals == ()``.
    """
    checked, unreadable, quoted_individuals = 0, [], 0
    datatype_named, unrepaired = 0, []
    for record in _records():
        try:
            tbox, abox = dl.parse_owl_functional(f"Ontology({record['owlfs']})")
        except dl.OwlFunctionalSyntaxError:
            continue
        kb = dl.kb_to_fol(tbox, abox)
        for node in (kb.formula, *kb.axioms):
            checked += 1
            quoted_individuals += _names_a_quoted_individual(node)
            parsed = api.parse_any(node.to_unicode_str())
            if parsed.ok and _formula_alpha_equal(node, parsed.formula):
                continue
            if _names_a_prefixed_datatype(node):
                # The data layer's documented limit: a built-in datatype is a
                # predicate NAMED `xsd:integer`, and a colon is no part of a
                # PREDICATE here (see tests/test_printed_text_reads_back.py).
                # The name is the ontology's own, so it is not rewritten; the
                # kit's sanitiser is the route to text, and it must work.
                datatype_named += 1
                sanitized, _mapping = sanitize_names(node)
                again = api.parse_any(sanitized.to_unicode_str())
                if not (again.ok and _formula_alpha_equal(sanitized, again.formula)):
                    unrepaired.append((record.get("id"), node.to_unicode_str()[:120]))
                continue
            unreadable.append((record.get("id"), node.to_unicode_str()[:120]))
    print(f"\nprinted images checked: {checked}; images with an individual "
          f"written in quotes: {quoted_individuals}; images naming a built-in "
          f"datatype (the data layer's documented limit, repaired by "
          f"sanitize_names): {datatype_named}")
    assert checked > 2000, f"only {checked} images checked; the scan is broken"
    assert quoted_individuals > 500, (
        f"only {quoted_individuals} images hold an individual written in quotes: "
        f"the quoted form is not being exercised")
    assert datatype_named > 0, (
        "no image names a built-in datatype: the data layer is not being exercised")
    assert not unreadable, (
        f"{len(unreadable)} printed images do not read back as the same "
        f"formula, e.g. {unreadable[:3]}")
    assert not unrepaired, (
        f"{len(unrepaired)} images naming a built-in datatype do not read back "
        f"even after sanitize_names, e.g. {unrepaired[:3]}")


@real_corpus
def test_the_whole_accepted_fragment_is_one_usable_knowledge_base():
    """The corpus as ONE document, which is what an ontology-sized question
    needs — and what ``_conjoin``'s left fold made impossible: at 1000
    conjuncts every node operation raised ``RecursionError``, and the accepted
    OEO fragment has over 3000.
    """
    axioms = []
    for record in _records():
        try:
            dl.parse_owl_functional(f"Ontology({record['owlfs']})")
        except dl.OwlFunctionalSyntaxError:
            continue
        axioms.append(record["owlfs"])
    document = "Ontology(\n" + "\n".join(f"  {a}" for a in axioms) + "\n)"
    tbox, abox = dl.parse_owl_functional(document)
    print(f"\none document: {len(tbox.inclusions)} concept inclusions, "
          f"{len(tbox.role_inclusions)} role inclusions, "
          f"{len(tbox.transitive_roles)} transitive roles, "
          f"{len(abox.concept_assertions)} class assertions, "
          f"{len(abox.role_assertions)} role assertions, "
          f"{len(abox.distinct_assertions)} distinctness assertions")
    assert len(tbox.inclusions) > 2000
    kb = dl.kb_to_fol(tbox, abox)
    text = kb.formula.to_unicode_str()
    print(f"the knowledge base prints in {len(text)} characters; "
          f"{len(kb.side_axioms)} side axioms")
    assert len(text) > 100000
    for export in (kb.formula.to_z3, kb.formula.to_dict):
        export()
    # TPTP: the data layer names a built-in datatype by its OWL name, and
    # ``xsd:decimal`` is no TPTP word, so the bare writer refuses it by name
    # (since 0.30.0 it writes no text a prover cannot read). The problem writer
    # that returns its name map is the route for a vocabulary like this one, and
    # it has to carry a formula of this size as well.
    with pytest.raises(NotImplementedError, match="is not a TPTP word"):
        kb.formula.to_tptp()
    problem, names = generate_tptp_problem_with_mapping([kb.formula])
    assert problem.count("fof(") >= 1 and len(problem) > 100000
    assert "xsd:" not in problem
    assert isinstance(hash(kb.formula), int)
    assert len(kb.premises) == 1 + len(kb.axioms)
