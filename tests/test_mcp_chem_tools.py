"""Tests for :mod:`unicode_fol_kit.mcp.chem_tools`.

Every expected value below is hand-derived from RDKit's documented,
deterministic SMILES atom/bond order (the same convention
``tests/test_chem.py`` already establishes: atom order is left-to-right
through the SMILES, so the "element letter + running per-element index"
domain naming is fully predictable by hand) and from the FOL semantics of
the formula under test, never copied from a first run of the code. Where a
derivation is non-trivial it is spelled out in the test's own docstring.

Skipped entirely (module-level ``importorskip``) on a machine without RDKit
— :mod:`unicode_fol_kit.mcp.chem_tools` itself imports fine without it (only
the functions that call ``chem.mol_to_structure`` need it, and each reports
a structured ``{"error": {"type": "ImportError", ...}}`` rather than raising
when it is missing), but every test here exercises real molecule
translation.
"""

import pytest

rdkit = pytest.importorskip("rdkit")

from unicode_fol_kit.mcp import chem_tools as ct

# The amide-bond pattern used throughout: "some carbon double-bonded to an
# oxygen and singly bonded to a nitrogen" — the textbook -C(=O)-N- amide
# linkage. Written directly in ChemLog's own lowercase-predicate TPTP
# spelling (dialect="tptp_bare" is check_molecule's default).
_AMIDE_PATTERN = (
    "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))"
)

# The identical pattern, written in the kit's OWN unicode surface syntax
# with kit-capitalised chemical predicate names (see the chem_tools module
# docstring's "Chemical formulas MUST be written in TPTP" — a non-tptp_bare
# dialect is honoured too, renamed to ChemLog spelling the same way). This
# is also the dialect with_spans=True actually supports (see the module
# docstring's "Spans" section) and, empirically, the one the real ChEBI
# campaign calls these tools with throughout its own pipeline.
_AMIDE_PATTERN_UNICODE = (
    "∃x∃y∃z (C(x) ∧ O(y) ∧ N(z) ∧ BDOUBLE(x,y) ∧ BSINGLE(x,z))"
)


# ---------------------------------------------------------------------------
# 1. molecule_to_structure
# ---------------------------------------------------------------------------

def test_molecule_to_structure_ethanol_domain_and_predicates():
    """"CCO" (ethanol) has 3 non-hydrogen atoms — two carbons, one oxygen
    (RDKit's atom order for "CCO" is C(0), C(1), O(2), giving domain
    {c1, c2, o1} — see test_chem.py's own worked ethanol derivation) — so
    domain_size must be 3, and "c/1"/"o/1" must both be among the nonempty
    predicates (c/1 has two rows, o/1 has one; the fully-empty canonical
    predicates like "s/1"/"p/1" must NOT appear)."""
    result = ct.molecule_to_structure("CCO")
    assert result["ok"] is True
    assert result["domain_size"] == 3
    assert result["structure"]["domain"] == ["c1", "c2", "o1"]
    assert "c/1" in result["nonempty_predicates"]
    assert "o/1" in result["nonempty_predicates"]
    assert "s/1" not in result["nonempty_predicates"]  # sulfur-free molecule
    assert "aromatic/1" in result["computed_predicates"]


def test_molecule_to_structure_invalid_naming_is_error_shape():
    """An unknown ``naming=`` is a caller/config mistake, not molecule DATA
    — it must come back as the documented-exception ``{"error": ...}``
    shape, not the argument/errors shape (that shape is reserved for bad
    SMILES/formula TEXT — see the module docstring's "Conventions")."""
    result = ct.molecule_to_structure("CCO", naming="bogus")
    assert "error" in result
    assert result["error"]["type"] == "ValueError"
    assert "bogus" in result["error"]["message"]


def test_molecule_to_structure_invalid_smiles_is_argument_shape():
    """RDKit's ``MolFromSmiles`` returns ``None`` (not an exception) for
    unparseable text; ``mol_to_structure`` turns that into a ``ValueError``,
    which this tool must reshape into the uniform ``ok=False``/``argument``
    shape (per the required Pflichttest: invalid SMILES and an unparseable
    formula both use the SAME shape)."""
    result = ct.molecule_to_structure("not-a-smiles-at-all(((")
    assert result["ok"] is False
    assert result["argument"] == "smiles"
    assert result["errors"][0]["message"]  # RDKit's own diagnosis, non-empty
    assert result["spec_topic"]


def test_molecule_to_structure_non_string_smiles_is_argument_shape_not_a_crash():
    """The same non-str-smiles contract fix as
    ``test_check_molecules_non_string_entry_is_a_per_item_error_not_a_crash``,
    exercised directly on ``molecule_to_structure`` (which calls
    ``chem.mol_to_structure`` itself rather than through the shared
    ``_build_structure`` helper) — a non-``str`` ``smiles`` must not leak
    ``mol_to_structure``'s raw :class:`TypeError`."""
    result = ct.molecule_to_structure(12345)
    assert result["ok"] is False
    assert result["argument"] == "smiles"
    assert "int" in result["errors"][0]["message"]


# ---------------------------------------------------------------------------
# 6. chemical_signature (tested early: check_molecule's own vocabulary tests
# below rely on the same 35-predicate signature this documents)
# ---------------------------------------------------------------------------

def test_chemical_signature_names_core_predicates():
    """The declared vocabulary must include the exact predicates the task
    brief names (c/o/n/bSINGLE/bDOUBLE), split correctly into
    stored/computed, with a dialect note pointing at tptp_bare."""
    result = ct.chemical_signature()
    assert result["ok"] is True
    predicates = result["signature"]["predicates"]
    for name in ("c", "o", "n", "bSINGLE", "bDOUBLE"):
        assert name in predicates
    # 40 = the 35 ChemLog predicates plus the five halogen letters the kit
    # adds (f/cl/br/i/at). Pinned against CHEMLOG_SIGNATURE itself rather
    # than a literal, so extending the vocabulary updates one place: the
    # point of this assertion is that the MCP tool publishes the WHOLE
    # signature, not that the signature has some particular size.
    from unicode_fol_kit.chem import CHEMLOG_SIGNATURE

    assert len(predicates) == len(CHEMLOG_SIGNATURE.predicates) == 40

    # in_ring/aromatic/same_fragment/carbon_connected need transitive
    # closure and are therefore COMPUTED, never stored — c/o/n/bSINGLE/
    # bDOUBLE are ordinary stored facts.
    assert "in_ring" in result["computed_predicates"]
    assert "aromatic" in result["computed_predicates"]
    assert "c" in result["stored_predicates"]
    assert "bDOUBLE" in result["stored_predicates"]
    assert set(result["stored_predicates"]) & set(result["computed_predicates"]) == set()
    assert set(result["stored_predicates"]) | set(result["computed_predicates"]) == set(predicates)

    assert result["groups"]["atom_types"] == [
        "c", "n", "o", "s", "p", "h", "f", "cl", "br", "i", "at"]
    assert "tptp_bare" in result["dialect_note"]


# ---------------------------------------------------------------------------
# 2. check_molecule — the amide-bond pattern, hand-verified against both
# molecules' RDKit-deterministic atom/bond structure.
# ---------------------------------------------------------------------------

def test_check_molecule_amide_pattern_true_for_glycylglycine():
    """"NCC(=O)NCC(=O)O" (glycylglycine) hand-derived atom order (left to
    right through the SMILES): N(0), C(1), C(2), O(3, =O on C2), N(4),
    C(5), C(6), O(7, =O on C6), O(8, the -OH). Per-element running index:
    n1=N0, c1=C1, c2=C2, o1=O3, n2=N4, c3=C5, c4=C6, o2=O7, o3=O8.

    Bonds: N0-C1, C1-C2 single; C2=O3 double (the first C=O); C2-N4 single
    (the peptide bond nitrogen); N4-C5, C5-C6 single; C6=O7 double (the
    carboxylic acid C=O); C6-O8 single (the carboxylic -OH).

    So c2 is double-bonded to o1 AND singly bonded to n2 — exactly the
    -C(=O)-N- amide pattern (the peptide bond joining the two glycine
    residues) — while c4 (the terminal carboxyl carbon) is double-bonded to
    an oxygen but only singly bonded to ANOTHER oxygen, not a nitrogen.
    Exactly one witness exists: {c: c2, o: o1, n: n2}.
    """
    result = ct.check_molecule(_AMIDE_PATTERN, "NCC(=O)NCC(=O)O")
    assert result == {"ok": True, "holds": True, "exhausted": False,
                      "steps": result["steps"],
                      "witness": {"c": "c2", "o": "o1", "n": "n2"}}


def test_check_molecule_amide_pattern_false_for_ethanol():
    """"CCO" (ethanol) has NO nitrogen atom at all (domain {c1, c2, o1}, all
    carbon/oxygen) — the amide pattern's ``n(N)`` conjunct can never be
    satisfied by any individual, so the pattern is unsatisfiable here
    regardless of ethanol's (single) C-O bond, and ``holds`` must be
    ``False``."""
    result = ct.check_molecule(_AMIDE_PATTERN, "CCO")
    assert result["ok"] is True
    assert result["holds"] is False
    assert result["exhausted"] is False
    assert "witness" not in result
    assert result["failing_conjunct"] is not None


def test_check_molecule_unparseable_formula_is_argument_shape():
    """Genuinely broken TPTP text (unbalanced/garbage) must come back as the
    uniform ``ok=False``/``argument="formula"`` shape, not a traceback."""
    result = ct.check_molecule("this is not ((valid tptp at all &&&", "CCO")
    assert result["ok"] is False
    assert result["argument"] == "formula"
    assert result["errors"]
    assert result["spec_topic"]


def test_check_molecule_invalid_smiles_is_argument_shape():
    """Pflichttest: invalid SMILES uses the SAME uniform shape (with
    "argument") as an unparseable formula — not the {"error": ...} shape."""
    result = ct.check_molecule(_AMIDE_PATTERN, "not-a-smiles-at-all(((")
    assert result["ok"] is False
    assert result["argument"] == "smiles"
    assert result["errors"]
    assert result["spec_topic"]


def test_check_molecule_uninterpreted_predicate_is_documented_error_shape():
    """A formula mentioning a predicate the CHEMLOG structure does not
    interpret (a hallucinated or not-yet-defined auxiliary class predicate)
    is a genuine vocabulary-mismatch bug in the caller's pipeline, not a bad
    SMILES/formula-text argument — it must surface as the documented
    ``{"error": {"type": "UninterpretedSymbol", ...}}`` shape, carrying the
    missing symbol/arity structurally."""
    result = ct.check_molecule(
        "?[X]: (someUndeclaredAuxiliaryPredicate(X) & c(X))", "CCO")
    assert "error" in result
    assert result["error"]["type"] == "UninterpretedSymbol"
    assert result["error"]["arity"] == 1
    assert "AuxiliaryPredicate" in result["error"]["symbol"]


def test_check_molecule_budget_exhaustion_reports_unknown_not_false():
    """KIT-PRINZIP: an undecided result must never be reported as ``False``.
    A budget of 1 step is nowhere near enough to decide the amide pattern
    against glycylglycine (a real evaluation needs dozens of steps for the
    quantifier search) — ``evaluate_detailed`` must come back with
    ``holds=None``/``exhausted=True``, and this tool must pass that through
    verbatim rather than collapsing it to ``False``."""
    result = ct.check_molecule(_AMIDE_PATTERN, "NCC(=O)NCC(=O)O", budget=1)
    assert result["ok"] is True
    assert result["holds"] is None
    assert result["exhausted"] is True
    assert "witness" not in result
    assert "failing_conjunct" not in result


# ---------------------------------------------------------------------------
# 3. check_molecules
# ---------------------------------------------------------------------------

def test_check_molecules_batch_summary_over_mixed_list():
    """A mixed batch of one satisfying molecule (glycylglycine — see the
    hand-derivation above), one non-satisfying molecule (ethanol, no
    nitrogen), and one bad SMILES must produce EXACTLY
    holds=1/fails=1/errors=1/unknown=0, with per-item entries carrying the
    same information check_molecule itself would."""
    result = ct.check_molecules(
        _AMIDE_PATTERN,
        ["NCC(=O)NCC(=O)O", "CCO", "not-a-smiles-at-all((("],
    )
    assert result["ok"] is True
    assert result["summary"] == {"total": 3, "holds": 1, "fails": 1,
                                 "unknown": 0, "errors": 1}
    by_smiles = {item["smiles"]: item for item in result["results"]}
    assert by_smiles["NCC(=O)NCC(=O)O"]["holds"] is True
    assert by_smiles["NCC(=O)NCC(=O)O"]["witness"] == {
        "c": "c2", "o": "o1", "n": "n2"}
    assert by_smiles["CCO"]["holds"] is False
    assert by_smiles["not-a-smiles-at-all((("]["ok"] is False
    assert "error" in by_smiles["not-a-smiles-at-all((("]


def test_check_molecules_bad_formula_aborts_before_any_molecule():
    """An unparseable formula fails once, up front — the top-level uniform
    shape, not a batch of per-molecule failures."""
    result = ct.check_molecules("garbage ((( &&&", ["CCO"])
    assert result["ok"] is False
    assert result["argument"] == "formula"


def test_check_molecules_empty_list_is_a_valid_empty_batch():
    result = ct.check_molecules(_AMIDE_PATTERN, [])
    assert result == {"ok": True, "results": [],
                      "summary": {"total": 0, "holds": 0, "fails": 0,
                                 "unknown": 0, "errors": 0}}


def test_check_molecules_non_string_entry_is_a_per_item_error_not_a_crash():
    """Regression test: before the fix, ``_build_structure`` passed a
    non-string ``smiles`` list entry straight into
    ``chem.mol_to_structure``, which raises a raw, undocumented
    :class:`TypeError` for anything that is not a ``str``/``Mol`` (hand-
    verified directly against ``chem.mol_to_structure(12345)`` before
    writing this test). That exception was not caught anywhere in
    ``check_molecules``'s per-molecule loop, so it propagated straight out
    of the tool call, losing the results for every OTHER (perfectly good)
    molecule in the same batch — a single caller-side mistake (e.g. an int
    slipping into a SMILES list from some upstream data-munging bug) tore
    down the whole call instead of producing one per-item error entry the
    way an unparseable SMILES STRING already does.

    Mixing a valid molecule (ethanol, "CCO"), a non-string entry (int
    ``12345``), and a second valid molecule (ethane, "CC") in one call must
    now come back as a normal batch: the two valid molecules get their
    ordinary results, and the int entry becomes exactly one
    ``{"ok": False, "error": ...}`` item — never an escaped exception.
    """
    result = ct.check_molecules(_AMIDE_PATTERN, ["CCO", 12345, "CC"])
    assert result["ok"] is True
    assert result["summary"]["total"] == 3
    assert result["summary"]["errors"] == 1
    by_smiles = {item["smiles"]: item for item in result["results"]}
    assert by_smiles["CCO"]["ok"] is True
    assert by_smiles["CC"]["ok"] is True
    bad = by_smiles[12345]
    assert bad["ok"] is False
    assert "TypeError" not in bad["error"]   # reshaped, not a raw traceback
    assert "int" in bad["error"]


# ---------------------------------------------------------------------------
# 4. explain_molecule_failure
# ---------------------------------------------------------------------------

def test_explain_molecule_failure_names_missing_nitrogen_for_ethanol():
    """Pflichttest: for ethanol the explanation must name the failing part.
    Ethanol has zero nitrogen atoms (``atoms_by_type["n"] == []``), so the
    rendered failing_conjunct — the whole amide-pattern existential, since
    its top node is a Quantifier chain rather than an And (see
    evaluate_detailed's own "failing_conjunct" contract: a non-And node is
    reported AS ITSELF) — must literally mention the ``n(`` nitrogen atom
    that has no witness, giving a caller everything needed to see WHY:
    cross-referencing the failing conjunct against ``atoms_by_type`` shows
    the missing element directly.
    """
    result = ct.explain_molecule_failure(_AMIDE_PATTERN, "CCO")
    assert result["ok"] is True
    assert result["holds"] is False
    assert result["atoms_by_type"]["n"] == []
    assert result["atoms_by_type"]["c"] == ["c1", "c2"]
    assert result["atoms_by_type"]["o"] == ["o1"]
    assert "n(" in result["failing_conjunct"]["unicode"]


def test_explain_molecule_failure_reports_atoms_and_bonds_for_glycylglycine():
    """The richer structural view (atoms grouped by type, per-atom facts,
    the bond list) for the molecule this pattern HOLDS of — hand-derived
    from the same atom/bond layout as
    ``test_check_molecule_amide_pattern_true_for_glycylglycine`` above: 4
    carbons, 2 nitrogens, 3 oxygens; c2 carries the properties
    ``["bSINGLE"]``-adjacent double bond to o1 (checked via the bonds list,
    since bond membership is not a unary "property" note); c1/c3 (the two
    -CH2- carbons) each have 2 hydrogens.
    """
    result = ct.explain_molecule_failure(_AMIDE_PATTERN, "NCC(=O)NCC(=O)O")
    assert result["ok"] is True
    assert result["holds"] is True
    assert result["domain_size"] == 9
    assert sorted(result["atoms_by_type"]["c"]) == ["c1", "c2", "c3", "c4"]
    assert sorted(result["atoms_by_type"]["n"]) == ["n1", "n2"]
    assert sorted(result["atoms_by_type"]["o"]) == ["o1", "o2", "o3"]
    assert "has_2_hs" in result["atom_properties"]["c1"]  # the -CH2- alpha carbon
    assert {"kind": "bDOUBLE", "atoms": ["c2", "o1"]} in result["bonds"]
    assert {"kind": "bSINGLE", "atoms": ["c2", "n2"]} in result["bonds"]


def test_explain_molecule_failure_invalid_smiles_is_argument_shape():
    result = ct.explain_molecule_failure(_AMIDE_PATTERN, "not-a-smiles(((")
    assert result["ok"] is False
    assert result["argument"] == "smiles"


# ---------------------------------------------------------------------------
# 5. simplify_definition
# ---------------------------------------------------------------------------

def test_simplify_definition_shrinks_pairwise_inequality_chain():
    """The literal distinct-witnesses redundancy pattern, at small n:
    ``∃x∃y∃z (c(x) ∧ c(y) ∧ c(z) ∧ x≠y ∧ x≠z ∧ y≠z)`` — 3 witnesses, all
    C(3,2)=3 pairwise inequalities written out. Under the (default here)
    ``all_different=True`` convention every one of those 3 ``≠`` literals is
    redundant (separately-∃-bound variables are already pairwise distinct),
    so ``simplify_for_checking`` must remove EXACTLY 3 literals, leaving
    only the 3 ``c(_)`` conjuncts — measurably smaller by construction, not
    merely "smaller in general"."""
    text = "?[X,Y,Z]: (c(X) & c(Y) & c(Z) & X!=Y & X!=Z & Y!=Z)"
    result = ct.simplify_definition(text)
    assert result["ok"] is True
    assert result["changed"] is True
    assert result["removed_count"] == 3
    assert len(result["removed"]) == 3
    assert "≠" not in result["after_unicode"]
    assert "≠" in result["before_unicode"]
    assert result["after_tptp"] is not None


def test_simplify_definition_after_tptp_round_trips_through_check_molecule():
    """The simplified formula's TPTP rendering must be genuinely re-usable —
    fed straight back into check_molecule, it must decide the SAME thing the
    all_different-aware evaluator decides for "at least 3 distinct carbons":
    True for propane (3 carbons, "CCC"), False for ethanol (2 carbons,
    "CCO"). This also exercises the case-preserving TPTP renderer: if it
    silently lowercased a chemical name (Node.to_tptp()'s own broken
    behaviour for a name like "bDOUBLE" — see the module docstring), a
    formula using such a name would fail this round trip with an
    UninterpretedSymbol error instead of a clean True/False.
    """
    text = "?[X,Y,Z]: (c(X) & c(Y) & c(Z) & X!=Y & X!=Z & Y!=Z)"
    simplified = ct.simplify_definition(text)
    propane = ct.check_molecule(simplified["after_tptp"], "CCC")
    ethanol = ct.check_molecule(simplified["after_tptp"], "CCO")
    assert propane["holds"] is True
    assert ethanol["holds"] is False


def test_simplify_definition_detects_count_pattern_on_original_not_simplified():
    """count_from_existential_chain only recognises a COMPLETE, EXACT
    instance of the distinct-witnesses pattern (every pairwise ≠ present);
    it must be checked against the ORIGINAL formula, not the already
    all_different-stripped one (which no longer has the ≠ literals and so
    would no longer match). "at least 3 distinct carbons" folds to
    "∃≥3 x c(x)" exactly."""
    text = "?[X,Y,Z]: (c(X) & c(Y) & c(Z) & X!=Y & X!=Z & Y!=Z)"
    result = ct.simplify_definition(text)
    assert result["count_pattern"]["detected"] is True
    assert result["count_pattern"]["folded_unicode"] == "∃≥3 x c(x)"


def test_simplify_definition_no_count_pattern_for_an_ordinary_definition():
    """A formula that is not the clean distinct-witnesses shape (here: just
    one existential over an amide-bond conjunction, no pairwise ≠ at all)
    must report count_pattern={"detected": False} — the folding is narrow by
    design and must not fire on unrelated formulas."""
    result = ct.simplify_definition(_AMIDE_PATTERN)
    assert result["count_pattern"] == {"detected": False}
    assert result["changed"] is False   # nothing to remove in this formula
    assert result["removed_count"] == 0


def test_simplify_definition_preserves_mixed_case_chemlog_names():
    """A regression guard for the exact bug this tool works around:
    ``Node.to_tptp()`` lowercases a predicate's ENTIRE name (turning
    "bDOUBLE" into "bdouble", a DIFFERENT, uninterpreted symbol), and
    silently mis-cases an already-quoted upper-case-led ChemLog name like
    "ChiralR" the same way through its own naive fallback. This test checks
    both: "bDOUBLE" survives simplification+rendering unchanged, and a
    trivial-equality removal (x=x) around "ChiralR" still renders correctly
    quoted and round-trips through parse_chemlog_tptp to an IDENTICAL AST.
    """
    text = "?[X,Y]: (c(X) & o(Y) & bDOUBLE(X,Y) & 'ChiralR'(X) & X=X)"
    result = ct.simplify_definition(text)
    assert "bDOUBLE" in result["after_tptp"]
    assert "bdouble" not in result["after_tptp"]
    assert "removed_count" in result and result["removed_count"] == 1  # the x=x

    from unicode_fol_kit import chem
    reparsed = chem.parse_chemlog_tptp(result["after_tptp"])
    expected_text = "?[X,Y]: (c(X) & o(Y) & bDOUBLE(X,Y) & 'ChiralR'(X))"
    expected = chem.parse_chemlog_tptp(expected_text)
    assert reparsed == expected


def test_simplify_definition_unparseable_formula_is_argument_shape():
    result = ct.simplify_definition("garbage ((( &&&")
    assert result["ok"] is False
    assert result["argument"] == "formula"


# ---------------------------------------------------------------------------
# 6. Spans (opt-in: with_spans=True on check_molecule / check_molecules /
#    explain_molecule_failure) — see the module docstring's "Spans" section.
# ---------------------------------------------------------------------------

def test_check_molecule_default_is_byte_identical_to_before_with_spans_existed():
    """The Pflichttest for the whole feature: a caller that never passes
    ``with_spans`` must see EXACTLY the same shape as before this parameter
    existed — in particular, no ``"span"`` key anywhere, not even a ``None``
    one, in either the omitted-argument or explicit-``False`` form."""
    omitted = ct.check_molecule(_AMIDE_PATTERN, "CCO")
    explicit = ct.check_molecule(_AMIDE_PATTERN, "CCO", with_spans=False)
    assert omitted == explicit
    assert "span" not in omitted["failing_conjunct"]


def test_check_molecule_with_spans_true_span_slices_the_original_text():
    """``with_spans=True`` on the kit's own unicode dialect: for ethanol
    (no nitrogen), the reported failing_conjunct's span, sliced out of the
    ORIGINAL formula text this call was given, must be a real substring of
    it — not merely resemble the re-rendered ``unicode`` field, which is
    free to re-space/re-bracket."""
    result = ct.check_molecule(_AMIDE_PATTERN_UNICODE, "CCO",
                               dialect="unicode", with_spans=True)
    assert result["ok"] is True
    assert result["holds"] is False
    span = result["failing_conjunct"]["span"]
    assert span is not None
    sliced = _AMIDE_PATTERN_UNICODE[span["start"]:span["end"]]
    assert sliced == span["text"]
    # Ethanol has no nitrogen at all, so blame cannot get past the outermost
    # quantifier chain (see test_explain_molecule_failure_names_missing_
    # nitrogen_for_ethanol's own comment on this same shape) -- the span
    # therefore covers the WHOLE formula.
    assert sliced == _AMIDE_PATTERN_UNICODE


def test_check_molecule_with_spans_true_narrows_to_the_specific_failing_conjunct():
    """A TOP-LEVEL conjunction of two independent existentials narrows blame
    (and hence the span) to whichever SIDE actually failed — the concrete
    payoff over reporting the whole formula's text: ethanol has carbons (the
    left conjunct holds) but no nitrogen (the right one fails), so the
    reported span must be exactly the right conjunct's own substring, with
    its surrounding parentheses excluded (they are not part of the AST
    node, only grouping punctuation around it)."""
    formula = "(∃x C(x)) ∧ (∃x N(x))"
    result = ct.check_molecule(formula, "CCO", dialect="unicode", with_spans=True)
    assert result["holds"] is False
    span = result["failing_conjunct"]["span"]
    assert formula[span["start"]:span["end"]] == "∃x N(x)"


def test_check_molecule_with_spans_true_tptp_bare_is_a_value_error_shape():
    """``with_spans=True`` together with this module's own default dialect
    (``tptp_bare``) is a caller/config mistake -- the span layer only covers
    the kit's own MSFLParser-backed syntax (see the module docstring) -- and
    must be reported as ``{"error": {"type": "ValueError", ...}}``, not a
    silent ``span: None`` a caller could mistake for "this conjunct simply
    has no span"."""
    result = ct.check_molecule(_AMIDE_PATTERN, "CCO", with_spans=True)
    assert result == {"error": result.get("error")}  # ONLY the error shape
    assert result["error"]["type"] == "ValueError"
    assert "tptp_bare" in result["error"]["message"]
    assert "with_spans" in result["error"]["message"]


def test_check_molecule_with_spans_true_unparseable_formula_is_argument_shape():
    """A genuine syntax error, even with with_spans=True, is the SAME
    uniform ok=False/argument shape :func:`check_molecule` always reports —
    a caller's ``result.get("ok") is False`` check must not have to branch
    on whether it asked for spans."""
    result = ct.check_molecule("this is not valid unicode syntax (((",
                               "CCO", dialect="unicode", with_spans=True)
    assert result["ok"] is False
    assert result["argument"] == "formula"
    assert result["errors"]
    assert result["spec_topic"]


def test_check_molecules_with_spans_true_attaches_span_to_every_failing_entry():
    result = ct.check_molecules(_AMIDE_PATTERN_UNICODE, ["CCO", "CC"],
                                dialect="unicode", with_spans=True)
    assert result["ok"] is True
    by_smiles = {item["smiles"]: item for item in result["results"]}
    for smiles in ("CCO", "CC"):
        entry = by_smiles[smiles]
        assert entry["holds"] is False
        assert entry["failing_conjunct"]["span"] is not None


def test_explain_molecule_failure_with_spans_true_attaches_span():
    result = ct.explain_molecule_failure(_AMIDE_PATTERN_UNICODE, "CCO",
                                         dialect="unicode", with_spans=True)
    assert result["ok"] is True
    assert result["holds"] is False
    span = result["failing_conjunct"]["span"]
    assert span is not None
    assert _AMIDE_PATTERN_UNICODE[span["start"]:span["end"]] == span["text"]


def test_check_molecule_with_spans_true_holds_true_has_no_failing_conjunct_key():
    """``holds is True`` never carries a ``failing_conjunct`` at all (with or
    without spans) — with_spans=True must not manufacture one."""
    result = ct.check_molecule(_AMIDE_PATTERN_UNICODE, "NCC(=O)NCC(=O)O",
                               dialect="unicode", with_spans=True)
    assert result["holds"] is True
    assert "failing_conjunct" not in result
    assert "witness" in result
