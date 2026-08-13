"""Molecules as finite FOL structures — the ChEBI2FOL model-checking side.

ChEBI2FOL (Nesy 2026 — this task's own commissioning paper) has an LLM
translate ChEBI class definitions to FOL and then classifies a molecule by
MODEL CHECKING that formula against the molecule, represented as a finite
FOL structure (atoms = individuals). The paper documents its formula side in
detail but its molecule-to-structure side only as a single worked prose
example (Section 3.1, ethanol) — no code. This subpackage is that missing
translation, in the vocabulary of ChemLog (Flügel et al. 2025, MIT
licence), the system the paper's own worked example is styled after:

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
  ChemLog's own TPTP-file spelling and the ChEBI2FOL paper's prose spelling
  of the identical vocabulary.

Why this exists (the paper's own documented bottlenecks)
-------------------------------------------------------------
The paper names three problems this subpackage speaks to directly: model-
checking timeouts are called "a major bottleneck" (addressed by
:class:`~unicode_fol_kit.semantics.structures.FiniteStructure`'s
candidate-set indexing, which this module's structures inherit for free);
precision of 0.0363 from over-general formulas (addressed elsewhere, by
tighter translation, not by this subpackage); and 89 of 136 failures from
"pure syntax" (addressed by :data:`CHEMLOG_SIGNATURE` catching an unknown
predicate or wrong arity before a definition ever reaches model checking).

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
    "CHEMLOG_SIGNATURE", "CHEMLOG_TO_PAPER", "PAPER_TO_CHEMLOG",
    "to_paper_naming", "to_chemlog_naming",
    # TPTP interop: the kit's importer inverts TPTP's case convention, so a
    # formula read from ChemLog/ChEBI2FOL TPTP needs its chemical vocabulary
    # renamed back before it lines up with a molecule structure.
    "parse_chemlog_tptp", "to_kit_names", "to_chemlog_names",
    "CHEMLOG_TO_KIT", "KIT_TO_CHEMLOG",
]
