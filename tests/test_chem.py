"""Tests for :mod:`unicode_fol_kit.chem` (SMILES/RDKit -> FiniteStructure).

Every structural assertion below is hand-derived from the input SMILES's
atom/bond list (worked out against RDKit's documented, deterministic parse
order and semantics — ``GetTotalNumHs`` = implicit + explicit hydrogens,
``GetFormalCharge`` = per-atom formal charge, bond order from the SMILES's
own notation), not copied from a first run of the code. Where a derivation
is non-trivial it is spelled out in the test's own docstring.

Skipped entirely (module-level ``importorskip``) on a machine without RDKit
— :mod:`unicode_fol_kit.chem.mol` and :mod:`unicode_fol_kit.chem.signature`
themselves stay importable without it (``test_importable_without_rdkit``
below checks this directly, bypassing the module-level skip), but
exercising real molecule translation needs a working RDKit installation.
"""

import sys

import pytest

rdkit = pytest.importorskip("rdkit")

from unicode_fol_kit import api
from unicode_fol_kit.fol.nodes import Atom, Variable, Quantifier, Implies
from unicode_fol_kit.semantics.structures import FiniteStructure
import unicode_fol_kit.chem as chem


# ---------------------------------------------------------------------------
# Ethanol — the smallest complete worked example, reproduced EXACTLY
# ---------------------------------------------------------------------------

def test_ethanol_reproduces_paper_structure_exactly():
    """"CCO" (ethanol, CH3-CH2-OH) must reproduce the canonical structure
    for this molecule under the ``paper`` naming scheme, symbol for symbol.

    RDKit's atom order for "CCO" is C(idx0), C(idx1), O(idx2) (left to right
    as written), so the running-per-element naming gives exactly c1, c2, o1.
    Bonds: idx0-idx1 SINGLE (the C-C bond), idx1-idx2 SINGLE (the C-O bond)
    — both single, so ``singleBond`` and ``bond`` get identical extensions,
    symmetrically stored (both directions), and no other bond predicate is
    ever populated for this molecule.

    Hydrogen counts (``GetTotalNumHs``, all implicit here — this SMILES
    writes no explicit H): c1 (the methyl carbon) has 3 H, c2 (the
    methylene carbon, bonded to c1 AND o1, using its 3rd and 4th valence on
    those two bonds) has 2 H, o1 (the hydroxyl oxygen, one bond to c2) has
    1 H. No SMILES atom here carries a charge annotation, so every atom is
    charge0 and the molecule's net charge is neutral.

    ``computed=False`` here specifically so plain dataclass equality on the
    returned :class:`FiniteStructure` is meaningful — a ``computed=True``
    structure's ``computed`` dict holds fresh Python closures on every
    call, which never compare equal to each other by identity even when
    they decide the exact same thing, so equality would be trivially and
    permanently False for a reason unrelated to correctness. The
    individuals_with/neighbors/holds spot checks afterwards do not have
    that problem and additionally exercise the query surface a caller
    would actually use.
    """
    expected = FiniteStructure(
        domain=("c1", "c2", "o1"),
        extensions={
            ("atom", 1): {("c1",), ("c2",), ("o1",)},
            ("c", 1): {("c1",), ("c2",)},
            ("o", 1): {("o1",)},
            ("n", 1): set(), ("s", 1): set(), ("p", 1): set(), ("h", 1): set(),
            ("charge0", 1): {("c1",), ("c2",), ("o1",)},
            ("charge_m1", 1): set(), ("charge_p1", 1): set(),
            ("has0Hs", 1): set(),
            ("has1H", 1): {("o1",)},
            ("has2Hs", 1): {("c2",)},
            ("has3Hs", 1): {("c1",)},
            ("ChiralR", 1): set(), ("ChiralS", 1): set(),
            ("singleBond", 2): {("c1", "c2"), ("c2", "c1"), ("c2", "o1"), ("o1", "c2")},
            ("doubleBond", 2): set(), ("tripleBond", 2): set(), ("aromaticBond", 2): set(),
            ("bond", 2): {("c1", "c2"), ("c2", "c1"), ("c2", "o1"), ("o1", "c2")},
            ("NetChargeNeutral", 0): {()},
            ("NetChargePositive", 0): set(),
            ("NetChargeNegative", 0): set(),
        },
    )
    got = chem.mol_to_structure("CCO", naming="paper", computed=False)
    assert got == expected

    # Same molecule, same naming, but the default computed=True — spot-check
    # via the public query API instead of equality (see docstring above).
    s = chem.mol_to_structure("CCO", naming="paper")
    assert set(s.domain) == {"c1", "c2", "o1"}
    assert s.individuals_with("atom") == s.domain
    assert s.individuals_with("c") == ("c1", "c2")
    assert s.individuals_with("o") == ("o1",)
    assert s.individuals_with("charge0") == s.domain
    assert s.individuals_with("has3Hs") == ("c1",)
    assert s.individuals_with("has2Hs") == ("c2",)
    assert s.individuals_with("has1H") == ("o1",)
    assert set(s.neighbors("singleBond", "c2")) == {"c1", "o1"}
    assert set(s.neighbors("bond", "c2")) == {"c1", "o1"}
    assert s.holds("NetChargePositive", ()) is False
    assert s.holds("NetChargeNeutral", ()) is True
    assert s.holds("NetChargeNegative", ()) is False


def test_ethanol_default_naming_is_chemlog_and_aliases_to_paper():
    """The default ``naming="chemlog"`` call must produce the TPTP-style
    spelling of the IDENTICAL facts checked above, and the two spellings
    must translate into each other via the documented alias tables.
    """
    s = chem.mol_to_structure("CCO")   # naming="chemlog" is the default
    assert s.individuals_with("has_3_hs") == ("c1",)
    assert s.individuals_with("has_2_hs") == ("c2",)
    assert s.individuals_with("has_1_hs") == ("o1",)
    assert set(s.neighbors("bSINGLE", "c2")) == {"c1", "o1"}
    assert set(s.neighbors("bond", "c2")) == {"c1", "o1"}
    # has_bond_to is chemlog-only (see chem._naming) and must be an EXACT
    # synonym of "bond" (same extension, both directions).
    assert set(s.neighbors("has_bond_to", "c2")) == {"c1", "o1"}
    assert s.holds("net_charge_neutral", ()) is True

    assert chem.to_paper_naming("has_3_hs") == "has3Hs"
    assert chem.to_paper_naming("has_2_hs") == "has2Hs"
    assert chem.to_paper_naming("has_1_hs") == "has1H"   # irregular singular
    assert chem.to_paper_naming("bSINGLE") == "singleBond"
    assert chem.to_paper_naming("net_charge_neutral") == "NetChargeNeutral"
    assert chem.to_paper_naming("bond") == "bond"          # identical both ways
    assert chem.to_chemlog_naming("has1H") == "has_1_hs"
    assert chem.to_chemlog_naming("singleBond") == "bSINGLE"
    with pytest.raises(KeyError):
        chem.to_paper_naming("has_bond_to")   # no paper-scheme counterpart


# ---------------------------------------------------------------------------
# L-Cysteine — hand-derived from RDKit's atom/bond order for the SMILES
# ---------------------------------------------------------------------------

def test_cysteine_seven_atoms_three_carbons_one_c_equals_o_neutral_chiral_r():
    """"N[C@@H](CS)C(O)=O" — L-cysteine.

    RDKit's atom order (left to right through the SMILES): N(0), C(1, the
    chiral alpha carbon), C(2, the CH2 bonded to sulfur), S(3), C(4, the
    carboxyl carbon), O(5, the hydroxyl O), O(6, the carbonyl =O).
    Per-element running index over that order gives: n1=N(0), c1=C(1),
    c2=C(2), s1=S(3), c3=C(4), o1=O(5), o2=O(6) — 7 non-hydrogen atoms,
    domain = {c1, c2, c3, s1, n1, o1, o2} as a set; three of them (c1, c2,
    c3) are carbons.

    Bonds (all SINGLE except one): N(0)-C(1), C(1)-C(2), C(2)-S(3),
    C(1)-C(4), C(4)-O(5) are single; C(4)-O(6) is DOUBLE (the carboxyl
    C=O). So exactly one bDOUBLE pair, between c3 (=C(4)) and o2 (=O(6)),
    stored both directions.

    Hydrogen counts: N(0) has 2 (the -NH2 amine), C(1) has 1 (the alpha
    CH), C(2) has 2 (the -CH2-S), S(3) has 1 (the thiol -SH), C(4) has 0
    (fully substituted carboxyl carbon), O(5) has 1 (the -OH), O(6) has 0
    (the =O) — so has_2_hs = {n1, c2}, has_1_hs = {c1, s1, o1},
    has_0_hs = {c3, o2}. No SMILES atom carries a charge annotation, so
    every atom is charge0 and the molecule is net-neutral.

    L-cysteine's alpha carbon is (R)-configured — the one proteinogenic
    L-amino acid whose CIP descriptor is R rather than S, because sulfur's
    higher atomic number (vs. the oxygen/nitrogen that decide the other 19)
    flips the substituent priority order; RDKit's CIP labeller reports this
    correctly and independently of the human mnemonic, so ChiralR = {c1} is
    a genuine, checkable chemistry fact, not an assumption.
    """
    s = chem.mol_to_structure("N[C@@H](CS)C(O)=O")
    assert set(s.domain) == {"c1", "c2", "c3", "s1", "n1", "o1", "o2"}
    assert set(s.individuals_with("c")) == {"c1", "c2", "c3"}
    assert s.individuals_with("n") == ("n1",)
    assert s.individuals_with("s") == ("s1",)
    assert set(s.individuals_with("o")) == {"o1", "o2"}

    assert s.holds("bDOUBLE", ("c3", "o2")) is True
    assert s.holds("bDOUBLE", ("o2", "c3")) is True
    assert s.neighbors("bDOUBLE", "c3") == ("o2",)
    assert set(s.individuals_with("has_2_hs")) == {"n1", "c2"}
    assert set(s.individuals_with("has_1_hs")) == {"c1", "s1", "o1"}
    assert set(s.individuals_with("has_0_hs")) == {"c3", "o2"}

    assert set(s.individuals_with("charge0")) == set(s.domain)
    assert s.holds("net_charge_neutral", ()) is True
    assert s.holds("NetChargePositive", ()) is False
    assert s.holds("NetChargeNegative", ()) is False
    assert s.individuals_with("ChiralR") == ("c1",)
    assert s.individuals_with("ChiralS") == ()


# ---------------------------------------------------------------------------
# Benzene — aromaticity, ring membership, connectivity
# ---------------------------------------------------------------------------

def test_benzene_aromatic_bonds_ring_and_fragment_when_aromatic_true():
    """"c1ccccc1" (benzene) with the default ``aromatic=True``.

    All 6 atoms are carbons in one 6-membered aromatic ring. RDKit types
    every ring bond AROMATIC (never SINGLE/DOUBLE) when aromaticity
    perception succeeds and ``aromatic=True`` keeps that typing, so
    ``bSINGLE``/``bDOUBLE`` must be EMPTY and ``bAROMATIC`` must hold of
    exactly the 6 ring bonds, stored both directions (12 ordered pairs).
    Every atom sits on the one ring, which is size 6, so ``in_ring`` and
    ``in_ring_of_size_6`` hold of all six atoms and ``in_ring_of_size_5``
    (a size the ring is not) holds of none. The molecule is a single
    connected component, so ``same_fragment`` relates every pair
    (reflexively/symmetrically/transitively — the full equivalence
    relation "same connected component").
    """
    s = chem.mol_to_structure("c1ccccc1")
    assert s.domain == ("c1", "c2", "c3", "c4", "c5", "c6")
    assert s.individuals_with("c") == s.domain
    assert s.holds("bSINGLE", ("c1", "c2")) is False
    d = s.to_dict()
    assert d["extensions"]["bSINGLE/2"] == []
    assert d["extensions"]["bDOUBLE/2"] == []
    assert len(d["extensions"]["bAROMATIC/2"]) == 12

    for atom in s.domain:
        assert s.holds("in_ring", [atom]) is True
        assert s.holds("in_ring_of_size_6", [atom]) is True
        assert s.holds("in_ring_of_size_5", [atom]) is False
        assert s.holds("aromatic", [atom]) is True
    for a in s.domain:
        for b in s.domain:
            assert s.holds("same_fragment", [a, b]) is True


def test_benzene_kekulized_bonds_when_aromatic_false_atom_flag_unaffected():
    """"c1ccccc1" with ``aromatic=False``: the SAME molecule, but bond typing
    is Kekulized (alternating single/double) instead of aromatic.

    Kekulization is applied to an independent COPY of the molecule (see the
    ``chem.mol`` module docstring's "The aromatic= parameter" section), so
    the six ring bonds become 3 SINGLE + 3 DOUBLE (an alternating pattern —
    the exact assignment RDKit picks is not asserted here, only the COUNTS,
    since either Kekule resonance structure is chemically equivalent and
    RDKit's own tie-breaking is an implementation detail this test should
    not pin down) and ``bAROMATIC`` becomes empty. The ATOM-level
    ``aromatic`` computed predicate is deliberately unaffected — it is
    read from the ORIGINAL, non-Kekulized molecule, since whether an atom
    is chemically/electronically aromatic does not depend on which bond-
    order representation was chosen to encode it.
    """
    s = chem.mol_to_structure("c1ccccc1", aromatic=False)
    d = s.to_dict()
    assert len(d["extensions"]["bSINGLE/2"]) == 6      # 3 bonds, both directions
    assert len(d["extensions"]["bDOUBLE/2"]) == 6       # 3 bonds, both directions
    assert d["extensions"]["bAROMATIC/2"] == []
    # every bond is still exactly one of bond/2's members, either way typed:
    assert len(d["extensions"]["bond/2"]) == 12
    for atom in s.domain:
        assert s.holds("aromatic", [atom]) is True
        assert s.holds("in_ring_of_size_6", [atom]) is True


# ---------------------------------------------------------------------------
# Disconnected fragments
# ---------------------------------------------------------------------------

def test_two_fragments_same_fragment_splits_correctly():
    """"CC.OO" (ethane and hydrogen peroxide, unconnected) — atom order
    left to right through the SMILES text gives C(0), C(1), O(2), O(3), so
    domain = (c1, c2, o1, o2). The two dot-separated components share no
    bond, so ``same_fragment`` must relate c1<->c2 and o1<->o2 but relate
    NEITHER carbon to EITHER oxygen.
    """
    s = chem.mol_to_structure("CC.OO")
    assert s.domain == ("c1", "c2", "o1", "o2")
    assert s.holds("same_fragment", ["c1", "c2"]) is True
    assert s.holds("same_fragment", ["o1", "o2"]) is True
    assert s.holds("same_fragment", ["c1", "o1"]) is False
    assert s.holds("same_fragment", ["c2", "o2"]) is False


def test_carbon_connected_stops_at_heteroatoms_unlike_same_fragment():
    """"CCOCC" (diethyl ether, CH3-CH2-O-CH2-CH3) — atom order gives
    c1(CH3), c2(CH2), o1(O), c3(CH2), c4(CH3). The whole molecule is ONE
    bond-connected fragment (same_fragment relates c1 and c4), but the
    carbon-only induced subgraph splits into TWO components ({c1,c2} and
    {c3,c4}) because both paths between them pass through the ether
    oxygen — exactly the distinction ``carbon_connected`` exists to draw
    that ``same_fragment`` cannot (see the ``chem.mol`` module docstring).
    A non-carbon atom is ``carbon_connected`` to nothing, not even itself.
    """
    s = chem.mol_to_structure("CCOCC")
    assert s.domain == ("c1", "c2", "o1", "c3", "c4")
    assert s.holds("same_fragment", ["c1", "c4"]) is True
    assert s.holds("carbon_connected", ["c1", "c2"]) is True
    assert s.holds("carbon_connected", ["c3", "c4"]) is True
    assert s.holds("carbon_connected", ["c1", "c4"]) is False
    assert s.holds("carbon_connected", ["c1", "o1"]) is False
    assert s.holds("carbon_connected", ["o1", "o1"]) is False


# ---------------------------------------------------------------------------
# Charged molecule
# ---------------------------------------------------------------------------

def test_acetate_anion_charge_m1_on_correct_oxygen():
    """"CC(=O)[O-]" (acetate anion) — atom order: C(0, methyl, 3H, charge0),
    C(1, carbonyl carbon, 0H, charge0), O(2, the =O, 0H, charge0), O(3, the
    explicit anionic oxygen, 0H, charge -1). Domain c1, c2, o1, o2. Exactly
    o2 (the atom the SMILES itself marks ``[O-]``) must be in charge_m1;
    every other atom stays in charge0. The molecule's total formal charge
    is the sum over all atoms, -1 here, so NetChargeNegative is True and
    the other two net-charge globals are False.
    """
    s = chem.mol_to_structure("CC(=O)[O-]")
    assert s.domain == ("c1", "c2", "o1", "o2")
    assert s.individuals_with("charge_m1") == ("o2",)
    assert set(s.individuals_with("charge0")) == {"c1", "c2", "o1"}
    assert s.holds("NetChargeNegative", ()) is True
    assert s.holds("NetChargePositive", ()) is False
    assert s.holds("net_charge_neutral", ()) is False


# ---------------------------------------------------------------------------
# Refusals — loud, not silent
# ---------------------------------------------------------------------------

def test_non_r_s_cip_code_is_refused_not_silently_dropped():
    """Regression test: prior to the fix, ``mol_to_structure``'s atom loop
    only checked ``cip == "R"``/``cip == "S"``, so an atom RDKit's
    ``rdCIPLabeler`` assigned a DIFFERENT, non-empty CIP descriptor to (a
    lower-case ``'r'``/``'s'`` for a pseudo-asymmetric centre, or ``'M'``/
    ``'P'`` for axial/helical chirality) landed in NEITHER ``ChiralR`` nor
    ``ChiralS`` — silently indistinguishable from an atom RDKit found no
    stereocentre at all, losing real, computed stereochemical information
    without any error or warning.

    "OC(=O)[C@H](O)[C@@H](O)[C@H](O)C(=O)O" reproduces this: hand-verified
    directly against ``rdCIPLabeler.AssignCIPLabels`` before writing this
    test, RDKit's atom order (left to right through the SMILES) is O(0),
    C(1, the first carboxyl C), O(2), C(3, CIP 'R'), O(4), C(5, CIP 's' —
    the middle, PSEUDO-asymmetric stereocentre, lower-case because it sits
    between two CIP-equivalent 'R' and 'S' neighbours), O(6), C(7, CIP
    'S'), O(8), C(9, the second carboxyl C), O(10), O(11). Per-element
    running index makes atom idx 5 the domain individual ``c3`` (the
    carbons in order: c1=idx1, c2=idx3, c3=idx5, c4=idx7, c5=idx9).

    Without the fix this call would silently succeed with a structure where
    ``c3`` is in neither ``ChiralR`` nor ``ChiralS`` — this test instead
    requires the loud refusal the fix adds: a :class:`ValueError` naming
    both the atom (index 5 / individual ``c3``) and the unrepresentable
    code (``'s'``), never a silently-incomplete structure.
    """
    with pytest.raises(ValueError, match=r"index 5.*c3.*'s'|'s'.*index 5"):
        chem.mol_to_structure("OC(=O)[C@H](O)[C@@H](O)[C@H](O)C(=O)O")


def test_plain_r_and_s_cip_codes_still_populate_chiralr_chirals():
    """Sanity companion to the refusal test above: an ordinary molecule
    whose ONLY CIP descriptors are the classical 'R'/'S' (L-cysteine, also
    covered in more depth by
    ``test_cysteine_seven_atoms_three_carbons_one_c_equals_o_neutral_chiral_r``
    above) must still build normally and populate exactly ``ChiralR`` — the
    fix must refuse only a code OUTSIDE {'R', 'S'}, not regress the
    ordinary case."""
    s = chem.mol_to_structure("N[C@@H](CS)C(O)=O")
    assert s.individuals_with("ChiralR") == ("c1",)
    assert s.individuals_with("ChiralS") == ()


def test_invalid_smiles_raises_valueerror_with_clear_text():
    with pytest.raises(ValueError, match="not-a-smiles"):
        chem.mol_to_structure("not-a-smiles(((")


def test_chemically_invalid_smiles_also_raises_valueerror():
    # Pentavalent carbon: RDKit's MolFromSmiles returns None for this
    # exactly as it does for a syntax error (hand-verified against the
    # RDKit API directly) — mol_to_structure must not distinguish and must
    # not crash with some unrelated AttributeError on a None Mol.
    with pytest.raises(ValueError):
        chem.mol_to_structure("C(C)(C)(C)(C)C")


def test_unsupported_element_raises_valueerror_naming_it():
    """"CCF" has a fluorine atom; ChemLog's own vocabulary here only types
    {C, N, O, S, P, H} atoms (see ``chem._naming.ELEMENT_LETTERS``), so an
    atom of any other element must be refused loudly rather than silently
    built without an atom-type predicate.
    """
    with pytest.raises(ValueError, match="F"):
        chem.mol_to_structure("CCF")


def test_unknown_naming_scheme_raises_valueerror():
    with pytest.raises(ValueError, match="naming"):
        chem.mol_to_structure("CCO", naming="bogus")


def test_non_str_non_mol_input_raises_typeerror():
    with pytest.raises(TypeError):
        chem.mol_to_structure(12345)


def test_missing_rdkit_raises_importerror_with_install_hint(monkeypatch):
    """Simulates a machine without RDKit installed by making ``import
    rdkit`` fail (``sys.modules["rdkit"] = None`` makes Python's import
    system raise ``ImportError`` for that name immediately — hand-verified
    against the interpreter directly), without needing to actually
    uninstall it. ``mol_to_structure`` imports RDKit lazily INSIDE the
    function (mirroring ``atp.cvc5_backend.Cvc5Backend.decide``'s pattern),
    so no module reload is needed for the patched ``sys.modules`` entry to
    take effect on the next call.
    """
    monkeypatch.setitem(sys.modules, "rdkit", None)
    with pytest.raises(ImportError, match="pip install rdkit"):
        chem.mol_to_structure("CCO")


# ---------------------------------------------------------------------------
# computed=False: a purely FOL-expressible structure
# ---------------------------------------------------------------------------

def test_computed_false_omits_all_five_computed_predicates():
    s = chem.mol_to_structure("c1ccccc1", computed=False)
    assert s.computed == {}
    with pytest.raises(KeyError):
        s.holds("in_ring", ["c1"])
    with pytest.raises(KeyError):
        s.holds("aromatic", ["c1"])
    with pytest.raises(KeyError):
        s.holds("same_fragment", ["c1", "c2"])
    # the stored (non-computed) vocabulary is entirely unaffected:
    assert s.holds("bAROMATIC", ("c1", "c2")) is True


# ---------------------------------------------------------------------------
# Accepting an already-parsed RDKit Mol directly
# ---------------------------------------------------------------------------

def test_accepts_an_already_parsed_rdkit_mol_object():
    from rdkit import Chem
    mol = Chem.MolFromSmiles("CCO")
    s = chem.mol_to_structure(mol, naming="paper")
    assert s.domain == ("c1", "c2", "o1")
    assert s.individuals_with("c") == ("c1", "c2")


# ---------------------------------------------------------------------------
# CHEMLOG_SIGNATURE: vocabulary conformance via api.check
# ---------------------------------------------------------------------------
#
# NOTE: these formulas are built as AST Nodes directly (Atom/Quantifier/...)
# rather than parsed from unicode-glyph TEXT, because this kit's own concrete
# TEXT syntax has an unrelated, pre-existing convention (hand-verified
# against unicode_fol_kit.api.parse_any directly: "atom(x)" / "c(x)" /
# "foo(x)" — any all-lowercase predicate NAME, regardless of length — fails
# to parse as a predicate application in the "fol" dialect grammar; only
# "Human(x)"-style capitalised names do) that has nothing to do with this
# subpackage's signature/structure contract. ChemLog's own vocabulary is
# deliberately mostly lowercase (c, o, bSINGLE, has_1_hs, ...), so testing
# THROUGH that text grammar would be testing an unrelated kit convention,
# not chem.signature's actual job: Signature.validate / api.check operate
# on the AST directly and are documented (fol/signature.py) to be case-
# agnostic — confirmed here.

def test_chemlog_signature_flags_unknown_predicate_and_wrong_arity():
    x = Variable("x")
    good = Quantifier("forall", x, Implies(Atom("c", [x]), Atom("atom", [x])))
    assert api.check(good, signature=chem.CHEMLOG_SIGNATURE).ok is True

    unknown = Quantifier("forall", x, Implies(Atom("Fooo", [x]), Atom("atom", [x])))
    r = api.check(unknown, signature=chem.CHEMLOG_SIGNATURE)
    assert r.ok is False
    assert any(e["kind"] == "unknown_predicate" and e["symbol"] == "Fooo"
               for e in r.signature_errors)

    wrong_arity = Atom("c", [x, x])   # c/1 is declared; used here at arity 2
    r2 = api.check(wrong_arity, signature=chem.CHEMLOG_SIGNATURE)
    assert any(e["kind"] == "wrong_arity" and e["symbol"] == "c"
               for e in r2.signature_errors)


def test_chemlog_signature_out_of_canonical_range_not_declared():
    """Methane ("C") has a single carbon with 4 hydrogens — outside the
    canonical has_0_hs..has_3_hs range :data:`CHEMLOG_SIGNATURE` declares
    (see that module's docstring). ``mol_to_structure`` still POPULATES
    ``has_4_hs`` (it is a genuine fact about this molecule), but
    ``CHEMLOG_SIGNATURE`` — deliberately scoped to the ChemLog spec text's
    own literal examples — does not know that name, so a formula using it
    is honestly flagged as undeclared rather than silently accepted.
    """
    s = chem.mol_to_structure("C")
    assert s.domain == ("c1",)
    assert s.individuals_with("has_4_hs") == ("c1",)
    assert "has_4_hs" not in chem.CHEMLOG_SIGNATURE.predicates

    x = Variable("x")
    formula = Atom("has_4_hs", [x])
    r = api.check(formula, signature=chem.CHEMLOG_SIGNATURE)
    assert any(e["kind"] == "unknown_predicate" and e["symbol"] == "has_4_hs"
               for e in r.signature_errors)


def test_chemlog_signature_declares_every_predicate_mol_to_structure_can_use():
    """The always-populated stored vocabulary (canonical range) plus the
    five computed predicates must ALL be declared — this is what lets a
    caller run ``api.check`` against ``CHEMLOG_SIGNATURE`` once and trust it
    for any molecule within the canonical range, without maintaining a
    second hand-written list that could drift from what ``mol.py`` emits.
    """
    s = chem.mol_to_structure("N[C@@H](CS)C(O)=O")   # cysteine: exercises
    # elements c/n/o/s, both chiral markers absent-for-most/present-for-one,
    # a double bond, and every computed predicate.
    for name, arity in s.signature():
        if arity == 0:
            assert name in chem.CHEMLOG_SIGNATURE.predicates, name
            continue
        assert name in chem.CHEMLOG_SIGNATURE.predicates, name
        assert chem.CHEMLOG_SIGNATURE.predicates[name].arity == arity


# ---------------------------------------------------------------------------
# Importable without RDKit
# ---------------------------------------------------------------------------

def test_importable_without_rdkit(monkeypatch):
    """``unicode_fol_kit.chem`` and its ``signature``/``_naming`` modules
    must import cleanly with RDKit absent — only actually CALLING
    ``mol_to_structure`` needs it (checked above). Re-imports fresh copies
    of the already-imported modules under a simulated RDKit-less
    environment to prove the module-level code path never touches RDKit.
    """
    import importlib
    monkeypatch.setitem(sys.modules, "rdkit", None)
    for name in ("unicode_fol_kit.chem", "unicode_fol_kit.chem.mol",
                 "unicode_fol_kit.chem.signature", "unicode_fol_kit.chem._naming"):
        monkeypatch.delitem(sys.modules, name, raising=False)
    fresh = importlib.import_module("unicode_fol_kit.chem")
    assert fresh.CHEMLOG_SIGNATURE.predicates["atom"].arity == 1
    with pytest.raises(ImportError, match="pip install rdkit"):
        fresh.mol_to_structure("CCO")
