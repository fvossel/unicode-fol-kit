"""SMILES / RDKit ``Mol`` in, a finite first-order structure out.

(The summary line above deliberately carries no cross-reference role:
autosummary truncates it at the first sentence end, and a dotted target like
``semantics.structures.FiniteStructure`` gets cut mid-role, leaving an
unterminated backtick in the generated table.)

This is the bridge model-checking-based classification needs: a molecule
*is* a finite FOL structure — atoms are individuals, and classification is
model CHECKING a class definition against that structure — but that framing
is usually stated in prose only, with no code for the molecule side, at
most a worked example done by hand (the one this module's ethanol test
reproduces exactly). :func:`mol_to_structure` is that missing translation:
SMILES (or an already-parsed RDKit ``Mol``) in, :class:`FiniteStructure`
out, in the ChemLog vocabulary (Flügel et al. 2025, MIT licence,
https://github.com/sfluegel05/chemlog-peptides) — see
:mod:`unicode_fol_kit.chem._naming` for exactly how that vocabulary is
spelled and why, and
:data:`unicode_fol_kit.chem.signature.CHEMLOG_SIGNATURE` for the matching
declared vocabulary ``api.check`` can validate a formula against.

RDKit is OPTIONAL
------------------
This module must stay importable without RDKit installed — the kit's
existing pattern for an optional binding (:mod:`unicode_fol_kit.atp.
cvc5_backend`) imports its dependency lazily inside the function that needs
it, not at module scope, and this module does the same via
:func:`_require_rdkit`. Install with ``pip install rdkit`` (or the
``unicode-fol-kit[chem]`` extra, once wired into the package's own
``pyproject.toml`` — that wiring is out of this module's scope). Calling
:func:`mol_to_structure` without RDKit installed raises :class:`ImportError`
naming exactly that install command, rather than failing on some unrelated
``NameError`` deep inside the function body.

Domain, naming, and hydrogen counting
---------------------------------------
The domain is every NON-hydrogen atom (ChemLog's own convention — hydrogens
are folded into per-heavy-atom hydrogen-COUNT predicates instead of being
individuals of their own, which is what keeps ``CCO`` a 3-individual
structure rather than a 9-individual one). Concretely: the input is first
normalised with ``Chem.RemoveHs`` — this folds any EXPLICITLY written
hydrogen atom (``"[H]C([H])([H])[H]"`` for methane, as opposed to the more
usual implicit ``"C"``) back into the heavy atom's implicit hydrogen count,
so the two spellings of the same molecule produce IDENTICAL structures
(hand-verified: both give the single individual ``c1`` with
``has_4_hs(c1)``). ``RemoveHs`` also compacts the remaining atom indices
while preserving their RELATIVE order (hand-verified against
``"C([H])(N)C(=O)O"`` — removing the explicit H at index 1 shifts every
later index down by exactly one, changing nothing else), which is what
makes the "stable name = element symbol + a running per-element index, in
input atom order" scheme deterministic: :func:`mol_to_structure` never
re-sorts or canonicalises atom order beyond what ``RemoveHs`` already does.
A residual ``H`` atom ``RemoveHs`` could not fold (an isotope-labelled
deuterium/tritium, or one RDKit keeps for stereo-perception reasons) is
refused with :class:`ValueError` rather than silently either being counted
as a heavy-atom individual (wrong: it would show up as a spurious ``h1``
individual with `h1` domain membership when the CHEMLOG-SIGNATUR contract's
own domain is "non-hydrogen atoms") or silently dropped from the hydrogen
count (wrong: an undercount no downstream consumer could detect).

"Deterministic" here means exactly one thing: calling :func:`mol_to_structure`
twice on the SAME input text (or the same already-parsed ``Mol``) always
names the same atom the same way. It is NOT a canonical, input-independent
molecule identifier — two DIFFERENT SMILES spellings of the identical
molecule can, and often do, assign the SAME name to two DIFFERENT atoms,
because the naming is a direct readout of RDKit's atom-parse order, which
itself is a readout of the order atoms are WRITTEN in the SMILES text, not
of the molecule's structure. Hand-verified: ``"CCO"`` (ethanol written
methyl-first) gives atom order C(methyl), C(methylene), O, so ``c1`` is the
METHYL carbon; ``"OCC"`` (the identical molecule, written oxygen-first)
gives atom order O, C(methylene), C(methyl), so ``c1`` is now the
METHYLENE carbon — the same name, two different atoms of the same
molecule, depending purely on which SMILES string was fed in. A caller
that needs atom identity to survive a re-serialisation, a canonicalisation
pass, or comparison across two independently-obtained SMILES strings for
"the same" molecule must not rely on these names for that — they identify
a position in ONE parse of ONE input text, nothing more.

Hydrogen count itself is ``Atom.GetTotalNumHs()`` with RDKit's own default
arguments — which, as hand-verified above, already sums implicit AND
explicit hydrogens correctly regardless of which way the input SMILES wrote
them, so no separate accounting is needed here.

Two naming schemes, chosen at the call site
----------------------------------------------
``naming="chemlog"`` (the default) spells every predicate the way the real
ChemLog TPTP files do (``bSINGLE``, ``has_1_hs``, ...); ``naming="paper"``
spells them the way prose write-ups of such class definitions do
(``singleBond``, ``has1H``, ...) — this is what lets the ethanol acceptance
test below reproduce a hand-written worked example VERBATIM rather than
merely "equivalently". See :mod:`unicode_fol_kit.chem._naming` for the exact
per-symbol rationale and the two schemes' full definitions, and
:mod:`unicode_fol_kit.chem.signature` for the ``CHEMLOG_TO_PAPER`` /
``PAPER_TO_CHEMLOG`` alias tables that translate between them after the
fact.

Always-populated predicates
------------------------------
Every predicate the chosen naming scheme's FIXED vocabulary declares (the
six atom-type letters, ``atom``, the four canonical hydrogen-count
predicates, the three canonical charge predicates, ``ChiralR``/``ChiralS``,
the four bond-type predicates, the ``bond``/``has_bond_to`` super-relations,
and the three net-charge globals) is given an EXPLICIT extension in the
returned structure — even an EMPTY one, for a molecule that does not
exhibit that feature. A sulfur-free molecule's structure still interprets
``s/1`` (as ``∅``), because :data:`unicode_fol_kit.chem.signature.
CHEMLOG_SIGNATURE` declares ``s/1`` as legitimate ChemLog vocabulary — a
formula asking ``s(x)`` about ethanol must evaluate to "false for every
``x``" (:meth:`FiniteStructure.holds` returning ``False``), not raise
``KeyError`` for an "uninterpreted" symbol the vocabulary in fact declares.
A molecule that genuinely needs a predicate OUTSIDE the canonical range
(``has_4_hs`` for methane's carbon; ``charge_m2`` for a doubly-anionic atom)
still gets it — the atom loop adds such a key on demand — it is simply not
PRE-populated as an empty default the way the canonical range is.

Why five predicates are COMPUTED, not stored (and why exactly these five)
------------------------------------------------------------------------------
:mod:`unicode_fol_kit.semantics.structures`'s own design note: some
properties of a finite structure are decidable ON it while being
inexpressible IN first-order logic OVER it. ChemLog hits this exactly
(their own external "BuildingBlock" predicate, computed in Python and
injected as ground facts) and this module follows the same pattern via
``FiniteStructure``'s ``computed=`` mechanism, so a definition may use
these predicates without the structure materialising their extension by
brute-force domain-squared enumeration:

* ``same_fragment/2`` — "connected in the bond graph" is the textbook
  FOL-inexpressible property: no fixed FOL formula (a fixed, finite
  quantifier count) can express "there exists a bond-path of ANY length
  between x and y", because for every candidate formula there is a large
  enough disconnected pair of molecules that formula cannot tell apart from
  a connected one (a compactness argument, the same one that rules out
  expressing "the graph is connected" in FOL generally). Computed here as
  the REFLEXIVE-symmetric-transitive closure of the bond relation (RDKit's
  ``GetMolFrags``) — deliberately the full equivalence relation ("same
  connected component"), not merely the bare transitive closure of the edge
  relation (which would leave an isolated, bond-free atom unrelated to
  itself).
* ``carbon_connected/2`` — the identical inexpressibility argument, applied
  to the induced subgraph of carbon atoms and carbon–carbon bonds only
  (chemically: "on the same carbon skeleton", ignoring heteroatom
  branches). Both endpoints must themselves be carbon; a non-carbon atom is
  ``carbon_connected`` to nothing, not even itself.
* ``in_ring/1`` — "lies on SOME cycle of the bond graph" is the same
  unbounded-length-path inexpressibility as ``same_fragment``, now applied
  to a cycle instead of a path. Computed via RDKit's SSSR ring perception
  (``GetRingInfo``).
* ``in_ring_of_size_N/1`` (``N`` in :data:`unicode_fol_kit.chem._naming.
  RING_SIZE_FAMILY`, i.e. 3..8) — for one FIXED ``N`` this predicate actually
  IS FOL-expressible in principle (∃ x₁…x_N pairwise-distinct with a bond
  cycling through x and all of them — a bounded quantifier count), so
  strictly it does not need to be computed. It is offered as a computed
  convenience anyway, for the same reason ChemLog itself precomputes ring
  membership rather than making every consumer spell out an N-quantifier
  cycle formula by hand: writing that axiom out is exactly the kind of
  syntax burden that makes hand- or machine-written class definitions fail
  on pure syntax before they are ever evaluated. A ring larger than the
  family's max (a macrocycle) is still correctly reported by the general
  ``in_ring/1`` (True); it simply has no ``in_ring_of_size_N`` member of
  its own — a real, documented limitation, not a silent one.
* ``aromatic/1`` — RDKit's aromaticity perception is a Hückel-rule
  ring-electron-counting algorithm, not a graph-local property any fixed-
  quantifier FOL formula over ``bond``/``bAROMATIC`` could re-derive from
  the stored bond-type facts alone even in principle (it would need to
  recognise arbitrarily-sized alternating ring systems). Kept computed
  (delegated to RDKit's own perception at query time) rather than
  duplicated as a second, stored copy of what ``bAROMATIC`` bond membership
  already encodes at the BOND level, so there is exactly one source of
  truth for "is this molecule's aromaticity" and it is never at risk of
  drifting out of sync with itself. Deliberately computed from the
  ORIGINAL (non-Kekulized) molecule regardless of the ``aromatic=`` bond-
  typing choice below — see that parameter's own note.

``computed=False`` omits all five entirely (``FiniteStructure.computed`` is
then empty), giving a structure whose ENTIRE vocabulary is genuinely FOL-
expressible over — useful e.g. for measuring how far a ChEBI class
definition gets using only facts a plain FOL formula could in principle
re-derive on its own.

The ``aromatic=`` parameter: bond typing, not atom typing
--------------------------------------------------------------
``aromatic=True`` (the default) keeps RDKit's own aromaticity perception in
the BOND types: a benzene ring's six bonds are all ``bAROMATIC`` and NONE
are ``bSINGLE``/``bDOUBLE``. ``aromatic=False`` Kekulizes a COPY of the
molecule first (``Chem.Kekulize(..., clearAromaticFlags=True)`` on a
``Chem.Mol(mol)`` copy, never the original), so those same six bonds become
an alternating ``bSINGLE``/``bDOUBLE`` pattern and ``bAROMATIC`` is empty
for that ring. The atom-level ``aromatic/1`` COMPUTED predicate is
unaffected either way (hand-verified: Kekulizing a copy clears aromaticity
flags on the COPY only, never the original ``mol`` the atom-level predicate
reads from) — a deliberate decoupling: whether an atom is (chemically,
electronically) aromatic is a fact about the molecule, independent of which
bond-order REPRESENTATION was chosen to encode it.

Unsupported input is refused, never approximated
------------------------------------------------------
An atom whose element is outside ChemLog's six-element vocabulary
(``{C, N, O, S, P, H}`` — see :mod:`unicode_fol_kit.chem._naming`) raises
:class:`ValueError` naming the element and its position, rather than
silently building an atom with no atom-type predicate at all (which would
make ``atom(x) ∧ ¬c(x) ∧ ¬n(x) ∧ …`` — a molecule with, say, a bromine —
look exactly like a modelling BUG rather than what it is: an out-of-scope
input). Likewise an unrecognised RDKit ``BondType`` (dative, quadruple, …)
is refused rather than silently dropped. An unparseable or chemically
invalid SMILES string (``Chem.MolFromSmiles`` returning ``None`` — RDKit
gives the identical ``None`` result for a syntax error and for a valence
error, e.g. a pentavalent carbon; hand-verified against both) raises
:class:`ValueError` with the offending text quoted.

The identical principle applies to stereochemistry. ``rdCIPLabeler`` (the
accurate CIP labeller ``mol_to_structure`` runs on every molecule — see
below) does not only assign the classical tetrahedral ``'R'``/``'S'``
labels this vocabulary's ``ChiralR``/``ChiralS`` predicates cover —
it also assigns lower-case ``'r'``/``'s'`` for a pseudo-asymmetric centre
(hand-verified: ``"OC(=O)[C@H](O)[C@@H](O)[C@H](O)C(=O)O"``'s middle
stereocentre gets ``_CIPCode == "s"``) and ``'M'``/``'P'`` for axial/helical
chirality (atropisomers, allenes). An atom with one of these non-``R``/
``S`` codes DOES have defined stereochemistry RDKit could determine — so
leaving both ``ChiralR`` and ``ChiralS`` unset for it, the way an earlier
version of this function did, would silently make it indistinguishable
from an atom with NO stereocentre at all, exactly the kind of information
loss this section is about. :func:`mol_to_structure` therefore raises
:class:`ValueError` for such an atom rather than adding it.

This is deliberately NOT configurable (no ``on_unsupported_stereo="raise"|
"ignore"`` escape hatch): unlike, say, an unrecognised element — which a
caller processing a large corpus might reasonably want to skip past — this
refusal already composes cleanly with the two per-molecule call sites that
matter (:func:`unicode_fol_kit.eval.datasets.c3po.score_definition` and
:mod:`unicode_fol_kit.mcp.chem_tools`'s ``check_molecules``), both of which
already catch exactly this :class:`ValueError` and report it as ONE
molecule's error entry, never aborting the whole run — the same handling
they already give an unsupported element or bond type. Adding a second,
silent way to lose the same information a caller could instead catch
:class:`ValueError` for themselves would only invite exactly the kind of
"a bit of both" approximation this kit's own conventions refuse elsewhere;
extending the ChemLog vocabulary with new predicates for these cases is
also deliberately out of scope here — ChemLog's own predicate list is a
fixed, external vocabulary this module targets, not one this module is
free to grow on its own judgement.
"""

from typing import Any, Dict, FrozenSet, Optional, Tuple

from ..semantics.structures import FiniteStructure
from . import _naming

__all__ = ["mol_to_structure"]

_RDKIT_INSTALL_HINT = (
    "unicode_fol_kit.chem.mol needs RDKit: pip install rdkit "
    "(or, once wired into this package's own extras: "
    "pip install 'unicode-fol-kit[chem]')"
)

Individual = str
Key = Tuple[str, int]


def _require_rdkit():
    """Import RDKit lazily; raise a clear, actionable :class:`ImportError` if
    it is absent, rather than a bare ``ModuleNotFoundError`` pointing at the
    import line inside this function (the same lazy-import-with-install-hint
    shape as :meth:`unicode_fol_kit.atp.cvc5_backend.Cvc5Backend.decide`)."""
    try:
        from rdkit import Chem, RDLogger
        from rdkit.Chem import rdCIPLabeler
    except ImportError as exc:
        raise ImportError(_RDKIT_INSTALL_HINT) from exc
    RDLogger.DisableLog("rdApp.*")   # library-internal parse/valence warnings
    return Chem, rdCIPLabeler


def mol_to_structure(
    mol_or_smiles: Any, *,
    naming: str = "chemlog",
    aromatic: bool = True,
    computed: bool = True,
) -> FiniteStructure:
    """Translate a molecule into a :class:`FiniteStructure` in the ChemLog
    (or, with ``naming="paper"``, the prose-spelling) vocabulary.

    Args:
        mol_or_smiles: a SMILES string, or an already-parsed
            ``rdkit.Chem.Mol`` (assumed already sanitised, as any ``Mol``
            coming out of ``Chem.MolFromSmiles``/``MolFromMolFile``/etc. is
            by default — this function does not re-sanitise one handed to
            it directly).
        naming: ``"chemlog"`` (default) or ``"paper"`` — see the module
            docstring's "Two naming schemes" section.
        aromatic: bond-typing choice — see the module docstring's
            ``aromatic=`` section. Does not affect the computed
            ``aromatic/1`` predicate.
        computed: whether to attach the five FOL-inexpressible-or-impractical
            computed predicates (``in_ring``, ``in_ring_of_size_N``,
            ``aromatic``, ``same_fragment``, ``carbon_connected``) — see the
            module docstring's "Why five predicates are COMPUTED" section.

    Returns:
        A :class:`FiniteStructure` whose domain is every non-hydrogen atom.

    Raises:
        ImportError: RDKit is not installed (message names the install
            command).
        ValueError: the SMILES text does not parse / is not a valid
            molecule; ``naming`` is neither ``"chemlog"`` nor ``"paper"``; an
            atom's element is outside ``{C, N, O, S, P, H}``; a bond has an
            RDKit ``BondType`` this vocabulary does not cover; RDKit's own
            ``RemoveHs`` could not fold away every hydrogen atom (see the
            module docstring's "residual H atom" note); or an atom carries a
            defined CIP stereo descriptor other than ``'R'``/``'S'`` (a
            pseudo-asymmetric ``'r'``/``'s'``, or axial/helical ``'M'``/
            ``'P'``) that ``ChiralR``/``ChiralS`` cannot represent (see the
            module docstring's "Unsupported input is refused, never
            approximated" section).
    """
    Chem, rdCIPLabeler = _require_rdkit()

    scheme = _naming.SCHEMES.get(naming)
    if scheme is None:
        raise ValueError(
            f"mol_to_structure: unknown naming={naming!r}, expected one of "
            f"{sorted(_naming.SCHEMES)}"
        )

    if isinstance(mol_or_smiles, str):
        mol = Chem.MolFromSmiles(mol_or_smiles)
        if mol is None:
            raise ValueError(
                f"mol_to_structure: RDKit could not parse {mol_or_smiles!r} "
                "as a molecule (invalid SMILES syntax, or a chemically "
                "invalid structure such as an over-valent atom — RDKit "
                "reports both identically as a parse failure)"
            )
    elif isinstance(mol_or_smiles, Chem.Mol):
        mol = mol_or_smiles
    else:
        raise TypeError(
            "mol_to_structure: mol_or_smiles must be a SMILES str or an "
            f"rdkit.Chem.Mol, got {type(mol_or_smiles).__name__}"
        )

    mol = Chem.RemoveHs(mol)
    for atom in mol.GetAtoms():
        if atom.GetSymbol() == "H":
            raise ValueError(
                f"mol_to_structure: atom index {atom.GetIdx()} is a hydrogen "
                "RDKit's RemoveHs could not fold away (an isotope label, or "
                "one RDKit keeps for stereochemistry) — this function's "
                "domain is exactly the non-hydrogen atoms and refuses to "
                "either count it as one or silently drop it from a "
                "hydrogen-count predicate"
            )
    Chem.GetSymmSSSR(mol)   # ensure ring perception is initialised regardless
                              # of whether the caller's own Mol already had it
    rdCIPLabeler.AssignCIPLabels(mol)   # accurate R/S (not raw CW/CCW parity)

    bond_type_key: Dict[object, str] = {
        Chem.BondType.SINGLE: "SINGLE", Chem.BondType.DOUBLE: "DOUBLE",
        Chem.BondType.TRIPLE: "TRIPLE", Chem.BondType.AROMATIC: "AROMATIC",
    }

    if aromatic:
        bond_mol = mol
    else:
        bond_mol = Chem.Mol(mol)
        Chem.Kekulize(bond_mol, clearAromaticFlags=True)

    # -- domain: element symbol + a running per-element index, in the
    # atom order RemoveHs left us with (see module docstring). ------------
    name_by_idx: Dict[int, Individual] = {}
    counters: Dict[str, int] = {}
    for atom in mol.GetAtoms():
        symbol = atom.GetSymbol()
        letter = _naming.ELEMENT_LETTERS.get(symbol)
        if letter is None:
            raise ValueError(
                f"mol_to_structure: unsupported element {symbol!r} at atom "
                f"index {atom.GetIdx()} — the ChemLog vocabulary this "
                f"function targets only types "
                f"{sorted(_naming.ELEMENT_LETTERS)} atoms; silently "
                "omitting this atom's type predicate would misrepresent "
                "the molecule, so this is refused instead"
            )
        counters[letter] = counters.get(letter, 0) + 1
        name_by_idx[atom.GetIdx()] = f"{letter}{counters[letter]}"

    domain: Tuple[Individual, ...] = tuple(
        name_by_idx[atom.GetIdx()] for atom in mol.GetAtoms())

    # -- unary/binary stored extensions, canonical range pre-populated ----
    unary: Dict[str, set] = {name: set() for name in (
        list(_naming.ELEMENT_LETTERS.values())
        + [_naming.ATOM_NAME]
        + [scheme.hs_name(n) for n in _naming.CANONICAL_HS_RANGE]
        + [scheme.charge_name(n) for n in _naming.CANONICAL_CHARGES]
        + [_naming.CHIRAL_R_NAME, _naming.CHIRAL_S_NAME]
    )}
    binary_names = [scheme.bond_type_names[k] for k in _naming.BOND_KINDS] \
        + [_naming.BOND_SUPER_NAME]
    if scheme.has_bond_to_name:
        binary_names.append(scheme.has_bond_to_name)
    binary: Dict[str, set] = {name: set() for name in binary_names}

    for atom in mol.GetAtoms():
        idx = atom.GetIdx()
        name = name_by_idx[idx]
        letter = _naming.ELEMENT_LETTERS[atom.GetSymbol()]
        unary.setdefault(letter, set()).add((name,))
        unary.setdefault(_naming.ATOM_NAME, set()).add((name,))
        hs_name = scheme.hs_name(atom.GetTotalNumHs())
        unary.setdefault(hs_name, set()).add((name,))
        charge_name = scheme.charge_name(atom.GetFormalCharge())
        unary.setdefault(charge_name, set()).add((name,))
        cip = atom.GetPropsAsDict().get("_CIPCode")
        if cip == "R":
            unary.setdefault(_naming.CHIRAL_R_NAME, set()).add((name,))
        elif cip == "S":
            unary.setdefault(_naming.CHIRAL_S_NAME, set()).add((name,))
        elif cip is not None:
            raise ValueError(
                f"mol_to_structure: atom index {idx} ({name}) carries a "
                f"defined CIP stereo descriptor {cip!r} this vocabulary "
                "cannot represent — ChemLog's ChiralR/ChiralS predicates "
                "only cover the classical tetrahedral 'R'/'S' labels, but "
                "rdCIPLabeler also assigns lower-case 'r'/'s' for "
                "pseudo-asymmetric centres and 'M'/'P' for axial/helical "
                "chirality (see the module docstring's 'Unsupported input "
                "is refused, never approximated' section). Silently "
                "leaving both ChiralR and ChiralS unset would make this "
                "atom indistinguishable from one with NO defined "
                "stereochemistry at all, so this is refused instead."
            )

    for bond in bond_mol.GetBonds():
        kind = bond_type_key.get(bond.GetBondType())
        if kind is None:
            raise ValueError(
                "mol_to_structure: unsupported bond type "
                f"{bond.GetBondType()!s} between atom indices "
                f"{bond.GetBeginAtomIdx()} and {bond.GetEndAtomIdx()} — "
                f"this vocabulary only covers {_naming.BOND_KINDS}"
            )
        a = name_by_idx[bond.GetBeginAtomIdx()]
        b = name_by_idx[bond.GetEndAtomIdx()]
        pred_name = scheme.bond_type_names[kind]
        binary.setdefault(pred_name, set()).update({(a, b), (b, a)})
        binary.setdefault(_naming.BOND_SUPER_NAME, set()).update({(a, b), (b, a)})
        if scheme.has_bond_to_name:
            binary.setdefault(scheme.has_bond_to_name, set()).update({(a, b), (b, a)})

    extensions: Dict[Key, FrozenSet] = {}
    for name, rows in unary.items():
        extensions[(name, 1)] = frozenset(rows)
    for name, rows in binary.items():
        extensions[(name, 2)] = frozenset(rows)

    net_total = Chem.GetFormalCharge(mol)
    extensions[(scheme.net_charge_neutral_name, 0)] = (
        frozenset({()}) if net_total == 0 else frozenset())
    extensions[(_naming.NET_CHARGE_POSITIVE_NAME, 0)] = (
        frozenset({()}) if net_total > 0 else frozenset())
    extensions[(_naming.NET_CHARGE_NEGATIVE_NAME, 0)] = (
        frozenset({()}) if net_total < 0 else frozenset())

    computed_preds: Dict[Key, object] = {}
    if computed:
        ri = mol.GetRingInfo()
        ring_sizes_by_name: Dict[Individual, FrozenSet[int]] = {}
        in_ring_by_name: Dict[Individual, bool] = {}
        aromatic_by_name: Dict[Individual, bool] = {}
        for idx, name in name_by_idx.items():
            sizes = frozenset(ri.AtomRingSizes(idx))
            ring_sizes_by_name[name] = sizes
            in_ring_by_name[name] = bool(sizes)
            aromatic_by_name[name] = mol.GetAtomWithIdx(idx).GetIsAromatic()

        fragment_by_name: Dict[Individual, int] = {}
        for fid, comp in enumerate(Chem.GetMolFrags(mol, asMols=False)):
            for idx in comp:
                fragment_by_name[name_by_idx[idx]] = fid

        carbon_idxs = {idx for idx, name in name_by_idx.items()
                       if mol.GetAtomWithIdx(idx).GetSymbol() == "C"}
        carbon_adj: Dict[int, list] = {idx: [] for idx in carbon_idxs}
        for bond in mol.GetBonds():
            a_idx, b_idx = bond.GetBeginAtomIdx(), bond.GetEndAtomIdx()
            if a_idx in carbon_idxs and b_idx in carbon_idxs:
                carbon_adj[a_idx].append(b_idx)
                carbon_adj[b_idx].append(a_idx)
        carbon_fragment_by_name: Dict[Individual, Optional[int]] = {}
        visited: set = set()
        next_cfid = 0
        for start in carbon_idxs:
            if start in visited:
                continue
            stack = [start]
            visited.add(start)
            while stack:
                cur = stack.pop()
                carbon_fragment_by_name[name_by_idx[cur]] = next_cfid
                for nb in carbon_adj[cur]:
                    if nb not in visited:
                        visited.add(nb)
                        stack.append(nb)
            next_cfid += 1
        for idx, name in name_by_idx.items():
            if idx not in carbon_idxs:
                carbon_fragment_by_name[name] = None

        computed_preds[("in_ring", 1)] = (
            lambda x, _d=in_ring_by_name: _d.get(x, False))
        for size in _naming.RING_SIZE_FAMILY:
            def _in_ring_of_size(x, _size=size, _d=ring_sizes_by_name):
                return _size in _d.get(x, frozenset())
            computed_preds[(f"in_ring_of_size_{size}", 1)] = _in_ring_of_size
        computed_preds[("aromatic", 1)] = (
            lambda x, _d=aromatic_by_name: _d.get(x, False))
        computed_preds[("same_fragment", 2)] = (
            lambda x, y, _d=fragment_by_name: _d.get(x) == _d.get(y))
        computed_preds[("carbon_connected", 2)] = (
            lambda x, y, _d=carbon_fragment_by_name:
                _d.get(x) is not None and _d.get(x) == _d.get(y))

    return FiniteStructure(domain=domain, extensions=extensions, computed=computed_preds)
