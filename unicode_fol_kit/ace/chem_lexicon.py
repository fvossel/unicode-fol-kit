"""The ChemLog vocabulary as an APE user lexicon — ACE about molecules.

:func:`chem_ulex` renders every speakable predicate of
:data:`unicode_fol_kit.chem.signature.CHEMLOG_SIGNATURE` as APE
``-ulextext`` entries, so ACE sentences can talk about molecules in plain
words while the DRS underneath carries the ChemLog symbols::

    from unicode_fol_kit.ace import ace_to_drs, chem_ulex
    drs = ace_to_drs("There is a carbon X1. There is an oxygen X2. "
                     "X1 bonds X2. X1 is aromatic.", ulex=chem_ulex())

The surface/symbol split is the whole point: the ENGLISH side says
"carbon", "bonds", "aromatic"; the LOGICAL side of each lexicon entry is
the ChemLog predicate itself (``c``, ``bond``, ``aromatic``), so what
arrives in the DRS is the declared chemistry vocabulary, not a parallel
spelling. Two shape differences against the raw signature are inherent to
ACE and documented rather than papered over:

- **Capitalization**: the kit's DRS/formula routes spell predicates in the
  kit convention (``c`` → ``C``, ``bond`` → ``Bond``, ``bSINGLE`` →
  ``BSINGLE``) — :func:`ace_kit_name` computes the arriving spelling for
  any ChemLog predicate.
- **Events**: an ACE verb always carries a Davidsonian event, so the
  binary ChemLog relations arrive with arity THREE (``Bond(e1, x1, x2)``).
  Projecting the event away (``∃e Bond(e, x, y)`` → ``bond(x, y)``) is a
  deliberate, separate step for the caller — this module does not do it
  silently.

The three NULLARY predicates (``net_charge_neutral``,
``NetChargePositive``, ``NetChargeNegative``) are unspeakable in ACE —
a sentence needs a subject — and are excluded by name
(:data:`CHEM_UNSPEAKABLE`); the coverage test pins that the three tables
plus this exclusion list tile the signature exactly, so a signature change
lands here loudly.

Category choices: elements and ``atom`` are NOUNS ("a carbon"), atom
properties are ADJECTIVES ("X1 is aromatic"), binary relations are
TRANSITIVE VERBS ("X1 bonds X2"). Hyphenated surfaces are ordinary ACE
words (probed: quoted-atom lexicon entries parse fine).
"""

from __future__ import annotations

from typing import Dict, Tuple

from .mapping import _kit_predicate
from .verbalize import _atom, _s_form

__all__ = ["chem_ulex", "ace_kit_name", "CHEM_NOUNS", "CHEM_ADJECTIVES",
           "CHEM_VERBS", "CHEM_UNSPEAKABLE"]


#: ChemLog predicate → ACE noun (singular surface; the plural adds ``s``).
CHEM_NOUNS: Dict[str, str] = {
    "at": "astatine",
    "atom": "atom",
    "br": "bromine",
    "c": "carbon",
    "cl": "chlorine",
    "f": "fluorine",
    "h": "hydrogen",
    "i": "iodine",
    "n": "nitrogen",
    "o": "oxygen",
    "p": "phosphorus",
    "s": "sulfur",
}

#: ChemLog predicate → ACE adjective ("X1 is aromatic.").
CHEM_ADJECTIVES: Dict[str, str] = {
    "ChiralR": "r-chiral",
    "ChiralS": "s-chiral",
    "aromatic": "aromatic",
    "charge0": "uncharged",
    "charge_m1": "negatively-charged",
    "charge_p1": "positively-charged",
    "has_0_hs": "zero-hydrogen",
    "has_1_hs": "one-hydrogen",
    "has_2_hs": "two-hydrogen",
    "has_3_hs": "three-hydrogen",
    "in_ring": "cyclic",
    "in_ring_of_size_3": "three-membered",
    "in_ring_of_size_4": "four-membered",
    "in_ring_of_size_5": "five-membered",
    "in_ring_of_size_6": "six-membered",
    "in_ring_of_size_7": "seven-membered",
    "in_ring_of_size_8": "eight-membered",
}

#: ChemLog predicate → (finite-singular, infinitive/plural) verb surfaces.
CHEM_VERBS: Dict[str, Tuple[str, str]] = {
    "bAROMATIC": ("aromatically-bonds", "aromatically-bond"),
    "bDOUBLE": ("double-bonds", "double-bond"),
    "bSINGLE": ("single-bonds", "single-bond"),
    "bTRIPLE": ("triple-bonds", "triple-bond"),
    "bond": ("bonds", "bond"),
    "carbon_connected": ("carbon-connects-to", "carbon-connect-to"),
    "has_bond_to": ("has-a-bond-to", "have-a-bond-to"),
    "same_fragment": ("shares-a-fragment-with", "share-a-fragment-with"),
}

#: The nullary ChemLog predicates — no ACE sentence can state a
#: subject-less proposition, so these have no surface, by name.
CHEM_UNSPEAKABLE = frozenset({
    "NetChargeNegative", "NetChargePositive", "net_charge_neutral",
})


def chem_ulex() -> str:
    """The whole speakable ChemLog vocabulary as ``-ulextext`` clauses."""
    lines = []
    for logical, noun in CHEM_NOUNS.items():
        lines.append(f"noun_sg({_atom(noun)}, {_atom(logical)}, neutr).")
        lines.append(
            f"noun_pl({_atom(_s_form(noun))}, {_atom(logical)}, neutr).")
    for logical, adj in CHEM_ADJECTIVES.items():
        lines.append(f"adj_itr({_atom(adj)}, {_atom(logical)}).")
    for logical, (finsg, infpl) in CHEM_VERBS.items():
        lines.append(f"tv_finsg({_atom(finsg)}, {_atom(logical)}).")
        lines.append(f"tv_infpl({_atom(infpl)}, {_atom(logical)}).")
    return "\n".join(sorted(lines))


def ace_kit_name(chemlog_name: str) -> str:
    """The kit-convention spelling a ChemLog predicate arrives under when
    an ACE sentence travels the DRS or formula route (``c`` → ``C``,
    ``bond`` → ``Bond``, ``bSINGLE`` → ``BSINGLE``)."""
    return _kit_predicate(chemlog_name)
