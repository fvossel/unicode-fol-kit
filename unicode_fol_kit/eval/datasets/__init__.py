"""NL→logic benchmark adapters, plus a known_bad / self-audit mechanic for
finding defective gold FOL annotations.

Every adapter normalises its source rows into the SAME
:class:`DatasetExample` shape (see its docstring for the field mapping each
one uses), so downstream evaluation code can iterate a mixed pipeline without
caring which dataset an example came from:

    from unicode_fol_kit.eval.datasets import load_folio, load_groves, audit_examples

    examples = list(load_folio("folio-validation.jsonl", known_bad_ids={"folio:17"}))
    report = audit_examples(examples)          # finds parse/well-formedness defects
    broken = [r for r in report if not r["ok"]]

The adapters (each module's docstring names its VERIFIED upstream source,
field schema, license, and every honest limitation; provenance is also
collected machine-readably in :data:`DATASET_INFO`):

- :mod:`~unicode_fol_kit.eval.datasets.folio` — FOLIO: premises/conclusion
  with entailment labels AND gold FOL.
- :mod:`~unicode_fol_kit.eval.datasets.malls` — MALLS: NL→FOL translation
  pairs (GPT-4-generated).
- :mod:`~unicode_fol_kit.eval.datasets.groves` — GROVES (this repo's author's
  dataset): NL→FOL translation pairs in this kit's own Unicode notation.
- :mod:`~unicode_fol_kit.eval.datasets.willow` — WillowNLtoFOL: NL→FOL
  translation pairs (one of GROVES's NL sources).
- :mod:`~unicode_fol_kit.eval.datasets.prontoqa` — ProntoQA (Logic-LM
  rendering): NL QA plus a Logic-LM DSL program per example, with
  :func:`~unicode_fol_kit.eval.datasets.prontoqa.parse_logic_program` (DSL →
  kit AST) and :func:`~unicode_fol_kit.eval.datasets.prontoqa.solve_example`
  (end-to-end deciding via ``api.prove``).
- :mod:`~unicode_fol_kit.eval.datasets.proofwriter` — ProofWriter, two
  routes: :func:`load_proofwriter` reads the flat tasksource mirror (NL text
  only, NO FOL gold; CWA/OWA label caveat in the module docstring), and
  :func:`load_proofwriter_structured` reads the structured OWA distribution
  and GENERATES FOL deterministically from the dataset's own triple/rule
  representations (marked ``meta["fol_generated"]``;
  :func:`~unicode_fol_kit.eval.datasets.proofwriter.solve_structured_example`
  decides each question against its OWA label).
- :mod:`~unicode_fol_kit.eval.datasets.logicnli` — LogicNLI: NLI-style FOL
  reasoning; the upstream structured logic annotation is preserved in
  ``meta``, not presented as gold FOL formula strings (it is not).
- :mod:`~unicode_fol_kit.eval.datasets.proverqa` — ProverQA: FOL-annotated QA
  whose gold formulas use the OPPOSITE naming convention from this kit's
  grammar (snake_case predicates, capitalised constants). The loader parses
  them with a dedicated import-time dialect grammar and re-emits kit
  notation (originals + injective name mapping in ``meta``;
  ``convert_fol=False`` restores the verbatim 0%-parse pass-through);
  :func:`~unicode_fol_kit.eval.datasets.proverqa.solve_example` decides each
  example end-to-end. Willow gets the same treatment for its ~1.2% tail via
  :func:`~unicode_fol_kit.eval.datasets.willow.repair_willow_formula`
  (NLTK-precedence reading, minimal renaming).

Per-dataset helper functions (converters, solvers) deliberately live on
their OWN modules rather than being re-exported here — two adapters
legitimately name their solver ``solve_example``, and a package-level
re-export would force one to shadow the other.

Deliberately NOT adapted (verified 2026-08-12, so the omission is a decision,
not an oversight): **AR-LSAT** (no logic annotation of any kind — Logic-LM
generates a Z3-style DSL at inference time, which is neither gold data nor
FOL; and the underlying LSAT passages are copyright-encumbered),
**LogicalDeduction** (BIG-bench; pure NL ordering puzzles, no formal
annotation — Logic-LM uses a runtime CSP DSL), and **FraCaS** (pure NL
premise/hypothesis/label NLI with no logic field in its DTD; public domain
and clean, so it would be the first candidate if this package ever grows a
pure-NLI adapter without FOL expectations).

No loader downloads anything — every one reads a LOCAL file the caller
already obtained (some upstreams distribute JSON arrays; each adapter's
docstring gives the one-line conversion recipe).

``known_bad`` (set by the loader from a caller-supplied ``known_bad_ids``) is
a CURATED flag; :func:`audit_examples` is an AUTOMATED, independent check
(does every gold FOL string parse, and is it well-formed?) — the two are
meant to be cross-checked against each other, not conflated as the same
signal.
"""

from ._base import DatasetExample, DATASET_INFO, audit_examples
from .folio import load_folio
from .malls import load_malls
from .groves import load_groves
from .willow import load_willow
from .prontoqa import load_prontoqa
from .proofwriter import load_proofwriter, load_proofwriter_structured
from .logicnli import load_logicnli
from .proverqa import load_proverqa
# C3PO is the first adapter whose gold is not a formula but an EXECUTABLE
# membership decision: a definition is scored by model-checking it against
# real molecule structures, so score_definition lives here beside the loader.
from .c3po import load_c3po, score_definition, DefinitionScore

__all__ = [
    "DatasetExample", "DATASET_INFO", "audit_examples",
    "load_folio", "load_malls", "load_groves", "load_willow",
    "load_prontoqa",
    "load_proofwriter", "load_proofwriter_structured",
    "load_logicnli", "load_proverqa",
    "load_c3po", "score_definition", "DefinitionScore",
]
