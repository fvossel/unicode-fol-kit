"""Shared naming-scheme machinery for :mod:`unicode_fol_kit.chem` — PRIVATE.

The ChemLog vocabulary this subpackage targets (Flügel et al. 2025, MIT
licence, https://github.com/sfluegel05/chemlog-peptides) is spelled two
different ways by the two kinds of source that describe it:

* **running prose** (as in a worked ethanol example) writes ``has3Hs`` /
  ``has2Hs`` / ``has1H`` (note the irregular singular at exactly one) and
  ``singleBond``;
* the actual **ChemLog TPTP source files** write ``has_1_hs`` / ``has_2_hs``
  / ``has_3_hs`` and ``bSINGLE``.

:mod:`unicode_fol_kit.chem.mol` has to pick ONE of these as what it actually
emits (silently supporting "a bit of both" would be exactly the kind of
unprincipled approximation this kit refuses), and
:mod:`unicode_fol_kit.chem.signature` has to publish a mapping between the
two so a caller who needs the other spelling is not stuck. Both modules
import this one so the naming rules are declared in exactly ONE place: were
``signature``'s alias table hand-written separately from what ``mol``
actually produces, the two would be free to drift out of sync with no test
able to catch it short of re-deriving both by hand. This module has NO
RDKit dependency (it deals in strings only) — it must stay importable
without RDKit installed, because :mod:`unicode_fol_kit.chem.signature`
(which needs it) explicitly must be.

**The default scheme is ``"chemlog"``** (the TPTP-file spelling), because
that is the vocabulary :mod:`unicode_fol_kit.chem.signature`'s
``CHEMLOG_SIGNATURE`` is built to validate against and because it is
internally uniform (one snake_case convention throughout) where the prose
spelling is not (see ``_hs_name_paper`` below). ``"paper"`` exists
specifically so a caller can reproduce the literal prose spelling — see
``mol.py``'s ethanol acceptance test.

Naming decisions spelled out (so a reviewer does not have to reverse-engineer
them from the code):

* **Hydrogen count.** ChemLog: ``has_{n}_hs`` uniformly. ``"paper"``:
  ``has{n}H`` at ``n == 1``, ``has{n}Hs`` otherwise — this is a
  GENERALISATION of the literal ``has3Hs``/``has2Hs``/``has1H`` (the only
  three values ethanol exhibits) to arbitrary ``n``; the prose spelling
  never shows ``n == 0`` or ``n > 3``, so extending the same
  singular-at-one rule to those is the only assumption made here, not a
  literal quote.
* **Formal charge.** IDENTICAL under both schemes: ``charge0`` at zero,
  ``charge_p{n}``/``charge_m{n}`` (``n = abs(charge)``) otherwise. The
  prose spelling only ever demonstrates ``charge0``; the ChemLog spec gives
  ``charge0, charge_m1, charge_p1 (bzw. chargeN)`` for the ChemLog side. The
  parenthetical generic form is read here as "continue the sign-letter
  pattern established by charge_m1/charge_p1 to any n" rather than as a
  THIRD, inconsistent bare ``chargeN`` spelling that would collide with the
  sign-letter convention already fixed at n=1 — the latter reading would
  leave the sign undetermined for exactly the cases (n>1) it is supposed to
  cover.
* **Bond types.** ChemLog: ``bSINGLE``/``bDOUBLE``/``bTRIPLE``/``bAROMATIC``
  (all four are literal ChemLog spec text). ``"paper"``: only
  ``singleBond`` is literally attested; ``doubleBond``/``tripleBond``/
  ``aromaticBond`` are this module's generalisation of that one example by
  analogy.
* **Net-charge globals.** ``NetChargePositive``/``NetChargeNegative`` are
  spelled IDENTICALLY in the ChemLog spec text and in prose (both
  CamelCase) — no alias needed. Only the neutral flag differs:
  ``net_charge_neutral`` (ChemLog, snake_case — matching the spec text
  verbatim, inconsistent as that is with the sibling predicates being
  CamelCase) vs. ``NetChargeNeutral`` (the ``"paper"`` scheme, CamelCase,
  matching its siblings and the literal prose spelling).
* **Element letters, ``atom``, ``ChiralR``/``ChiralS``, the ``bond``
  super-relation.** Spelled identically by both sources — no alias table
  entry is needed for these beyond the identity pairing (included below for
  completeness, so a caller can look ANY known predicate up in one table
  without having to special-case "well, THIS one doesn't need translating").
* **``has_bond_to``.** ChemLog-only: the spec text lists it as a second name
  for the same bond-existence super-relation ``bond`` alongside ``bond``
  itself (their exact relationship undocumented beyond "binaere: ... bond
  (Oberrelation), has_bond_to" in the spec text) — both are populated as
  IDENTICAL extensions under the ``"chemlog"`` scheme. The prose spelling
  never mentions a second name at all, so the ``"paper"`` scheme simply
  omits it; it has no alias-table counterpart (deliberately absent, not an
  oversight — see :mod:`unicode_fol_kit.chem.signature`).

The computed predicates (:mod:`unicode_fol_kit.chem.mol`'s ``in_ring`` /
``in_ring_of_size_N`` / ``aromatic`` / ``same_fragment`` / ``carbon_
connected``) are this module's OWN addition beyond either source's literal
vocabulary, so they are scheme-INVARIANT (same spelling always) and are not
part of the alias table below — an identity mapping would carry no
information a lookup failure doesn't already convey by raising.
"""

from dataclasses import dataclass
from typing import Callable, Dict, Optional, Tuple

__all__: Tuple[str, ...] = ()   # private module — nothing meant for reuse outside chem/

# -----------------------------------------------------------------------
# Fixed, scheme-invariant vocabulary
# -----------------------------------------------------------------------

#: RDKit element symbol -> ChemLog atom-type letter (identical in both
#: schemes, and in the literal worked ethanol example: M(c), M(o)).
ELEMENT_LETTERS: Dict[str, str] = {
    "C": "c", "N": "n", "O": "o", "S": "s", "P": "p", "H": "h",
}

ATOM_NAME = "atom"
CHIRAL_R_NAME = "ChiralR"
CHIRAL_S_NAME = "ChiralS"
BOND_SUPER_NAME = "bond"
NET_CHARGE_POSITIVE_NAME = "NetChargePositive"
NET_CHARGE_NEGATIVE_NAME = "NetChargeNegative"

#: The four RDKit bond-order "kinds" this vocabulary covers, by a
#: scheme-independent short key (NOT an RDKit ``BondType`` — this module has
#: no RDKit dependency; ``mol.py`` maps ``rdkit.Chem.BondType`` values onto
#: these keys itself).
BOND_KINDS: Tuple[str, ...] = ("SINGLE", "DOUBLE", "TRIPLE", "AROMATIC")

#: The hydrogen-count / formal-charge values every structure ``mol.py``
#: builds interprets EXPLICITLY (even as an empty extension) regardless of
#: whether the particular molecule exhibits them — see ``mol.py``'s module
#: docstring, "always-populated predicates", for why: a formula asking
#: ``s(x)`` of a sulfur-free molecule must get "false everywhere", not a
#: ``KeyError`` for an uninterpreted symbol that the ChemLog vocabulary in
#: fact declares. These two ranges match the ChemLog spec text's OWN
#: examples verbatim (``has_0_hs``..``has_3_hs``; ``charge0``, ``charge_m1``,
#: ``charge_p1``) rather than some wider guess — a molecule that genuinely
#: needs e.g. ``has_4_hs`` (methane's carbon) or ``charge_m2`` still gets
#: that predicate populated (``mol.py``'s atom loop adds keys on demand), it
#: is just not PRE-populated as an empty default the way 0..3 / -1/0/1 are.
CANONICAL_HS_RANGE: Tuple[int, ...] = (0, 1, 2, 3)
CANONICAL_CHARGES: Tuple[int, ...] = (0, -1, 1)

#: Concrete ring sizes ``mol.py`` exposes as their own unary predicate
#: (``in_ring_of_size_3`` .. ``in_ring_of_size_8``), alongside the fully
#: general ``in_ring`` (any size). Range chosen to cover the ring sizes that
#: actually recur in organic/bio-organic chemistry — cyclopropane through
#: cyclooctane, which already includes every common aromatic and
#: heteroaromatic ring (5- and 6-membered). A macrocycle bigger than 8 is
#: still correctly reported by ``in_ring`` (True) but has no
#: ``in_ring_of_size_N`` member of its own — a real but narrow limitation,
#: not a silent one: nothing claims a size-12 ring is a size-8 ring.
RING_SIZE_FAMILY: Tuple[int, ...] = (3, 4, 5, 6, 7, 8)


def _hs_name_chemlog(n: int) -> str:
    return f"has_{n}_hs"


def _hs_name_paper(n: int) -> str:
    return f"has{n}H" if n == 1 else f"has{n}Hs"


def _charge_name(n: int) -> str:
    if n == 0:
        return "charge0"
    return f"charge_{'p' if n > 0 else 'm'}{abs(n)}"


@dataclass(frozen=True)
class NamingScheme:
    """One consistent spelling of the ChemLog vocabulary.

    ``bond_type_names`` maps each :data:`BOND_KINDS` key to that scheme's
    predicate name; ``has_bond_to_name`` is ``None`` under the ``"paper"``
    scheme (see the module docstring's "``has_bond_to``" bullet).
    """

    key: str
    hs_name: Callable[[int], str]
    charge_name: Callable[[int], str]
    net_charge_neutral_name: str
    bond_type_names: Dict[str, str]
    has_bond_to_name: Optional[str]


CHEMLOG = NamingScheme(
    key="chemlog",
    hs_name=_hs_name_chemlog,
    charge_name=_charge_name,
    net_charge_neutral_name="net_charge_neutral",
    bond_type_names={
        "SINGLE": "bSINGLE", "DOUBLE": "bDOUBLE",
        "TRIPLE": "bTRIPLE", "AROMATIC": "bAROMATIC",
    },
    has_bond_to_name="has_bond_to",
)

PAPER = NamingScheme(
    key="paper",
    hs_name=_hs_name_paper,
    charge_name=_charge_name,
    net_charge_neutral_name="NetChargeNeutral",
    bond_type_names={
        "SINGLE": "singleBond", "DOUBLE": "doubleBond",
        "TRIPLE": "tripleBond", "AROMATIC": "aromaticBond",
    },
    has_bond_to_name=None,
)

#: ``naming=`` argument -> scheme, consulted by ``mol.mol_to_structure``.
SCHEMES: Dict[str, NamingScheme] = {"chemlog": CHEMLOG, "paper": PAPER}


def chemlog_predicate_arities() -> Dict[str, int]:
    """Every predicate ``mol_to_structure(naming="chemlog")`` may populate,
    mapped to its arity — the vocabulary
    :data:`unicode_fol_kit.chem.signature.CHEMLOG_SIGNATURE` declares.

    Includes the computed predicates (present when ``computed=True``, the
    default) alongside the stored ones, since both are equally part of what
    a formula checked against ``CHEMLOG_SIGNATURE`` is allowed to mention —
    :class:`~unicode_fol_kit.fol.signature.Signature` has no notion of
    "stored vs. computed", only "declared vs. not".
    """
    out: Dict[str, int] = {}
    for letter in ELEMENT_LETTERS.values():
        out[letter] = 1
    out[ATOM_NAME] = 1
    for n in CANONICAL_HS_RANGE:
        out[CHEMLOG.hs_name(n)] = 1
    for n in CANONICAL_CHARGES:
        out[CHEMLOG.charge_name(n)] = 1
    out[CHIRAL_R_NAME] = 1
    out[CHIRAL_S_NAME] = 1
    for kind in BOND_KINDS:
        out[CHEMLOG.bond_type_names[kind]] = 2
    out[BOND_SUPER_NAME] = 2
    assert CHEMLOG.has_bond_to_name is not None
    out[CHEMLOG.has_bond_to_name] = 2
    out[CHEMLOG.net_charge_neutral_name] = 0
    out[NET_CHARGE_POSITIVE_NAME] = 0
    out[NET_CHARGE_NEGATIVE_NAME] = 0
    # computed
    out["in_ring"] = 1
    for size in RING_SIZE_FAMILY:
        out[f"in_ring_of_size_{size}"] = 1
    out["aromatic"] = 1
    out["same_fragment"] = 2
    out["carbon_connected"] = 2
    return out


def _build_chemlog_to_paper() -> Dict[str, str]:
    """The alias table :mod:`unicode_fol_kit.chem.signature` publishes,
    derived from the two :class:`NamingScheme` objects above rather than
    hand-duplicated, so it cannot drift from what ``mol.py`` actually emits
    (see the module docstring's opening paragraph)."""
    out: Dict[str, str] = {}
    for letter in ELEMENT_LETTERS.values():
        out[letter] = letter
    out[ATOM_NAME] = ATOM_NAME
    out[CHIRAL_R_NAME] = CHIRAL_R_NAME
    out[CHIRAL_S_NAME] = CHIRAL_S_NAME
    out[BOND_SUPER_NAME] = BOND_SUPER_NAME
    out[NET_CHARGE_POSITIVE_NAME] = NET_CHARGE_POSITIVE_NAME
    out[NET_CHARGE_NEGATIVE_NAME] = NET_CHARGE_NEGATIVE_NAME
    out[CHEMLOG.net_charge_neutral_name] = PAPER.net_charge_neutral_name
    for n in CANONICAL_HS_RANGE:
        out[CHEMLOG.hs_name(n)] = PAPER.hs_name(n)
    for n in CANONICAL_CHARGES:
        out[CHEMLOG.charge_name(n)] = PAPER.charge_name(n)
    for kind in BOND_KINDS:
        out[CHEMLOG.bond_type_names[kind]] = PAPER.bond_type_names[kind]
    # has_bond_to deliberately excluded: no paper-scheme counterpart exists.
    return out


CHEMLOG_TO_PAPER: Dict[str, str] = _build_chemlog_to_paper()
PAPER_TO_CHEMLOG: Dict[str, str] = {v: k for k, v in CHEMLOG_TO_PAPER.items()}
