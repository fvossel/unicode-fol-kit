"""The ``ace`` subpackage — Attempto Controlled English, via APE.

ACE is a controlled natural language with exactly ONE reading per sentence,
fixed by documented interpretation rules rather than by a statistical guesser
— which makes it the natural English-shaped INPUT format for a kit whose other
readers (TPTP, Prover9, SMT-LIB, SBN, CASL, …) already assume that a text
means one thing. The reference parser APE is driven as an external subprocess
(LGPL; never vendored, never reimplemented — see
:mod:`unicode_fol_kit.ace.runner`'s module docstring for why a partial APE
clone would be worse than none).

What works today (milestone ACE-1) is the TPTP route: ACE text → APE → TPTP →
:func:`unicode_fol_kit.fol.tptp_input.parse_tptp` → kit formulas, plus a
mechanical per-sentence coverage report. Three outcomes, none silent:

>>> from unicode_fol_kit.ace import ace_to_fol   # doctest: +SKIP
>>> [f.to_unicode_str() for f in ace_to_fol("Every man waits.")]  # doctest: +SKIP
['∀a (Man(a) → ∃b Predicate1(b, wait, a))']

- a sentence that is not ACE raises :class:`~unicode_fol_kit.ace.runner.AceParseError`
  with APE's own diagnosis (position, token, repair hint);
- an ACE sentence whose DRS uses modality, negation as failure, a question or
  a command raises :class:`~unicode_fol_kit.ace.runner.AceTptpUnsupportedError`
  — Attempto's OWN TPTP translator refuses those, and the kit routes them
  into its modal family in milestone ACE-3 instead of mistranslating today;
- a plural cardinality ("at least 3 men") survives only REIFIED on THIS
  route (Attempto's export kept verbatim) and is flagged by
  :func:`~unicode_fol_kit.ace.runner.ace_coverage` (``reified_cardinality``)
  — the DRS and formula routes below carry the counting force (ACE-4/5).

Since milestone ACE-2/3 the DRS itself is first-class, and three routes share
one vocabulary (pinned against each other by a Z3 differential over the whole
corpus — see ``tests/test_ace_mapping.py``):

- :func:`~unicode_fol_kit.ace.runner.ace_to_fol` — Attempto's own TPTP,
  through the kit's reader (fast, but only what THEIR translator covers);
- :func:`~unicode_fol_kit.ace.mapping.ace_to_drs` — APE's DRS read 1:1
  (:func:`~unicode_fol_kit.ace.drs_reader.parse_ape_drs`) and mapped onto
  :mod:`unicode_fol_kit.drt`'s core, every condition reported
  (:class:`~unicode_fol_kit.ace.mapping.DrsMapping`), nothing dropped
  silently — since ACE-5 including plurals and cardinalities, collectively,
  on the ``Card``/``Part`` conditions;
- :func:`~unicode_fol_kit.ace.translate.ace_to_formula` — straight to one
  kit formula, INCLUDING what a DRS cannot hold: ACE's four modal boxes
  become □/◇/Ⓞ/Ⓟ, a wh-question an open formula, a yes/no question a
  closed one with its interrogative force kept on ``kind``, the
  ``exactly``/``at most`` maximality a counting quantifier, and arithmetic
  kit terms (decided by :func:`~unicode_fol_kit.atp.z3_arith.is_valid_arith`).

Still refused everywhere, by name: commands and negation as failure (both
honestly undecided — no milestone).

Since ACE-6 the pipeline also runs BACKWARDS:
:func:`~unicode_fol_kit.ace.verbalize.drs_to_ace` verbalizes a kit DRS as
ACE text plus the user-lexicon entries that carry its content words, and
:func:`~unicode_fol_kit.ace.verbalize.ace_round_trip` is the machine
self-check — text through APE and back, judged by Z3 (the whole mappable
corpus closes the loop). :func:`~unicode_fol_kit.ace.chem_lexicon.chem_ulex`
renders the ChemLog signature as such a lexicon, so ACE sentences can talk
about molecules in plain words ("a carbon", "bonds", "aromatic") while the
DRS underneath carries the declared chemistry vocabulary.
"""

from .drs_reader import (
    AceAtom, AceCommand, AceCondList, AceDrs, AceDrsUnreadError, AceExpr,
    AceImpl, AceInt, AceModal, AceNaf, AceNamed, AceNeg, AceOr, AceQuestion,
    AceReal, AceString, AceTermApp, AceVar, parse_ape_drs,
)
from .mapping import (
    AceUnsupportedError, ConditionReport, DrsMapping, ace_to_drs,
    condition_statistics, map_ace_drs,
)
from .runner import (
    AceError, AceParseError, AceTptpUnreadError, AceTptpUnsupportedError,
    ApeMessage, ApeResult, ApeUnavailableError, CoverageRow, ace_coverage,
    ace_to_fol, ape_available, run_ape,
)
from .translate import AceFormula, ace_drs_to_formula, ace_to_formula
from .verbalize import (
    AceRoundTrip, AceText, AceVerbalizationError, ace_round_trip, drs_to_ace,
)
from .chem_lexicon import ace_kit_name, chem_ulex

__all__ = [
    # the engine and the three routes
    "ape_available", "run_ape", "ace_to_fol", "ace_to_drs", "ace_to_formula",
    "ace_coverage", "map_ace_drs", "ace_drs_to_formula", "parse_ape_drs",
    "condition_statistics",
    # the reverse direction (ACE-6)
    "drs_to_ace", "ace_round_trip", "chem_ulex", "ace_kit_name",
    # results and reports
    "ApeResult", "ApeMessage", "CoverageRow", "DrsMapping",
    "ConditionReport", "AceFormula", "AceText", "AceRoundTrip",
    # the 1:1 DRS model
    "AceDrs", "AceVar", "AceNamed", "AceInt", "AceReal", "AceString",
    "AceExpr", "AceTermApp", "AceAtom", "AceNeg", "AceNaf", "AceImpl",
    "AceOr", "AceModal", "AceQuestion", "AceCommand", "AceCondList",
    # errors
    "AceError", "ApeUnavailableError", "AceParseError",
    "AceTptpUnsupportedError", "AceTptpUnreadError", "AceDrsUnreadError",
    "AceUnsupportedError", "AceVerbalizationError",
]
