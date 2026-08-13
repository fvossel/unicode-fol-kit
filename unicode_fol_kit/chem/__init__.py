"""Molecules as finite FOL structures — the model-checking side.

A chemical class definition written in FOL classifies a molecule by MODEL
CHECKING that formula against the molecule, represented as a finite FOL
structure (atoms = individuals). The formula side of such a pipeline is
what usually gets documented in detail; the molecule-to-structure side
tends to exist only as a single worked prose example (ethanol) — no code.
This subpackage is that missing translation, in the vocabulary of ChemLog
(Flügel et al. 2025, MIT licence,
https://github.com/sfluegel05/chemlog-peptides):

    >>> from unicode_fol_kit.chem import mol_to_structure, CHEMLOG_SIGNATURE
    >>> ethanol = mol_to_structure("CCO")             # SMILES -> FiniteStructure
    >>> ethanol.individuals_with("c")                 # the two carbons
    ('c1', 'c2')
    >>> from unicode_fol_kit import api
    >>> api.check("∀x (c(x) → atom(x))", signature=CHEMLOG_SIGNATURE).ok
    True

Scope
-----
* :mod:`.mol` — :func:`mol_to_structure`: SMILES or an ``rdkit.Chem.Mol`` in,
  a :class:`~unicode_fol_kit.semantics.structures.FiniteStructure` out. RDKit
  is an OPTIONAL dependency (``pip install rdkit``); importing this
  subpackage never requires it, only calling :func:`mol_to_structure` does.
* :mod:`.signature` — :data:`CHEMLOG_SIGNATURE`, the same vocabulary as a
  first-class kit :class:`~unicode_fol_kit.fol.signature.Signature`
  (for ``api.check(formula, signature=CHEMLOG_SIGNATURE)``), plus the
  :data:`CHEMLOG_TO_PAPER` / :data:`PAPER_TO_CHEMLOG` alias tables between
  ChemLog's own TPTP-file spelling and the prose spelling of the identical
  vocabulary.

Why this exists (the bottlenecks this pipeline hits)
----------------------------------------------------------
Three problems recur in a pipeline of this shape, and this subpackage
speaks to each directly: model-checking timeouts are the major bottleneck
(addressed by
:class:`~unicode_fol_kit.semantics.structures.FiniteStructure`'s
candidate-set indexing, which this module's structures inherit for free);
over-general formulas, whose precision cost stays invisible until it is
measured against a corpus (addressed elsewhere, by tighter translation, not
by this subpackage); and failures on pure syntax, which dominate the rest
(addressed by :data:`CHEMLOG_SIGNATURE` catching an unknown predicate or
wrong arity before a definition ever reaches model checking).

What this subpackage does NOT do
--------------------------------------
It does not translate natural-language class definitions to FOL (that is
the rest of the kit — parsing, ``api.check``, the prover backends), and it
does not itself run model checking (that is
:mod:`unicode_fol_kit.semantics.model_eval` / the Tarskian evaluator over
the :class:`FiniteStructure` this subpackage builds). It is exactly the one
missing piece: molecule in, structure out, in a vocabulary the rest of the
kit already knows how to check formulas against.
"""

from .mol import mol_to_structure
from .cache import StructureCache, StructureBuildError
from .signature import (
    CHEMLOG_SIGNATURE, CHEMLOG_TO_PAPER, PAPER_TO_CHEMLOG,
    to_paper_naming, to_chemlog_naming,
)

from .interop import (
    parse_chemlog_tptp, to_kit_names, to_chemlog_names,
    CHEMLOG_TO_KIT, KIT_TO_CHEMLOG,
)

__all__ = [
    "mol_to_structure",
    "StructureCache", "StructureBuildError",
    "CHEMLOG_SIGNATURE", "CHEMLOG_TO_PAPER", "PAPER_TO_CHEMLOG",
    "to_paper_naming", "to_chemlog_naming",
    # TPTP interop: the kit's importer inverts TPTP's case convention, so a
    # formula read from ChemLog TPTP needs its chemical vocabulary renamed
    # back before it lines up with a molecule structure.
    "parse_chemlog_tptp", "to_kit_names", "to_chemlog_names",
    "CHEMLOG_TO_KIT", "KIT_TO_CHEMLOG",
]
