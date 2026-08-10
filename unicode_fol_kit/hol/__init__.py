"""Higher-order / Isabelle / THF exporters: shallow semantical embeddings (SSE).

This subpackage *emits* Benzmüller-style shallow embeddings of the toolkit's non-fuzzy
logics into higher-order logic — as complete, self-contained problem files for an
external prover (Leo-III / Satallax on TPTP **THF**, or Isabelle/HOL theories for
Sledgehammer). The exporters only emit; a successful emission means "here is a sound
problem an external prover *may* discharge", never "decided" — first-order modal logic,
FOL and SOL are all undecidable (FOL and the standard first-order modal logics are still
semi-decidable — validity is recursively enumerable — whereas full second-order validity
is not even semi-decidable).

The optional :mod:`~unicode_fol_kit.hol.isabelle_runner` is the other half: if a local
Isabelle/HOL is installed, it actually *runs* it on the emitted modal theories
(prove-battery + nitpick) and reads a VALID / INVALID / UNKNOWN verdict off the build —
turning "emit" into "proven / refuted". It is sound (Isabelle's kernel certifies the
proof; nitpick reports only genuine counter-models) and, necessarily, incomplete.

Modules:

- :mod:`~unicode_fol_kit.hol.isabelle_modal` — a real, loadable Isabelle/HOL theory for
  the **full modal family** (alethic, epistemic/doxastic over *agent-indexed* relations,
  deontic, temporal), with all lifted operators, frame + domain axioms, the lifted
  formula, and a real ``lemma``. Replaces the old alethic-only skeleton.
- :mod:`~unicode_fol_kit.hol.thf_modal` — the full-modal-family TPTP **THF** export
  (agent-indexed epistemic/doxastic, deontic, temporal), extending the alethic-only
  ``qml.to_thf_modal``.
- :mod:`~unicode_fol_kit.hol.classical` — FOL and MSFOL → THF / Isabelle.
- :mod:`~unicode_fol_kit.hol.isabelle_relevant` — relevant logic B (Routley–Meyer
  shallow embedding, frame conditions as lemma premises) + the runner's
  ``isabelle_decide_relevant``.
- :mod:`~unicode_fol_kit.hol.isabelle_substructural` — ILL / Lambek **derivation
  replay**: the sequent rules as an ``inductive`` derivability predicate and the
  concrete Python-found derivation replayed as a machine-checked lemma.
- :mod:`~unicode_fol_kit.hol.manyvalued` — three-valued K3 / LP → THF / Isabelle,
  generalised to ANY finite :class:`~unicode_fol_kit.semantics.matrix.TruthMatrix`
  (including Belnap–Dunn FDE) via ``to_thf_matrix`` / ``to_isabelle_matrix``.
- :mod:`~unicode_fol_kit.hol.secondorder` — second-order logic → THF / Isabelle
  (native higher-order predicate quantification; standard semantics).
- :mod:`~unicode_fol_kit.hol.intuitionistic` — intuitionistic propositional logic → HOL
  via the Gödel–McKinsey–Tarski translation into S4 then the alethic SSE.
- :mod:`~unicode_fol_kit.hol.deepshallow` — the **deep + maximal-shallow +
  minimal-shallow** embeddings of a non-classical logic *with machine-checked
  faithfulness proofs* between them (Benzmüller, arXiv:2502.19311). Unlike the
  emit-only SSE above, these theories are verified end to end by the Isabelle runner.
"""

from .isabelle_modal import (
    to_isabelle_modal, isabelle_modal_theory, ISABELLE_TACTICS, modal_axiom_names,
    BRIDGES,
)
from .isabelle_runner import (
    find_isabelle, isabelle_available, isabelle_decide_modal, isabelle_decide_fol,
    isabelle_decide_counterfactual, isabelle_decide_relevant,
    check_theory, IsabelleInstall, IsabelleNotAvailable, BuildResult,
    ModalVerdict, FolVerdict, DEFAULT_METHODS,
)
from .isabelle_relevant import to_isabelle_relevant
from .isabelle_substructural import (
    to_isabelle_ill, ill_derivation_theory,
    to_isabelle_lambek, lambek_derivation_theory,
)
from .thf_modal import to_thf_modal_full, thf_full_definitions, thf_full_frame_axioms
from .classical import to_thf_fol, to_isabelle_fol, to_thf_msfol, to_isabelle_msfol
from .manyvalued import (
    to_thf_k3lp, to_isabelle_k3lp,
    to_thf_k3lp_entailment, to_isabelle_k3lp_entailment, SYSTEMS,
    to_thf_matrix, to_isabelle_matrix,
    to_thf_matrix_entailment, to_isabelle_matrix_entailment,
)
from .secondorder import to_thf_so, to_isabelle_so
from .intuitionistic import (
    gmt_translate, to_thf_intuitionistic, to_isabelle_intuitionistic,
    gmt_is_s4_valid, gmt_validity_matches_int_valid,
)
from .deepshallow import (
    modal_faithfulness_theory, modal_to_deep,
    intuitionistic_faithfulness_theory, int_to_deep,
    conditional_faithfulness_theory, counterfactual_to_deep,
    relevant_faithfulness_theory, rel_to_deep,
)

__all__ = [
    "to_isabelle_modal", "isabelle_modal_theory", "ISABELLE_TACTICS",
    "modal_axiom_names", "BRIDGES",
    "find_isabelle", "isabelle_available", "isabelle_decide_modal",
    "isabelle_decide_fol", "isabelle_decide_counterfactual",
    "isabelle_decide_relevant", "check_theory",
    "IsabelleInstall", "IsabelleNotAvailable", "BuildResult",
    "ModalVerdict", "FolVerdict", "DEFAULT_METHODS",
    "to_isabelle_relevant",
    "to_isabelle_ill", "ill_derivation_theory",
    "to_isabelle_lambek", "lambek_derivation_theory",
    "to_thf_modal_full", "thf_full_definitions", "thf_full_frame_axioms",
    "to_thf_fol", "to_isabelle_fol", "to_thf_msfol", "to_isabelle_msfol",
    "to_thf_k3lp", "to_isabelle_k3lp",
    "to_thf_k3lp_entailment", "to_isabelle_k3lp_entailment", "SYSTEMS",
    "to_thf_matrix", "to_isabelle_matrix",
    "to_thf_matrix_entailment", "to_isabelle_matrix_entailment",
    "to_thf_so", "to_isabelle_so",
    "gmt_translate", "to_thf_intuitionistic", "to_isabelle_intuitionistic",
    "gmt_is_s4_valid", "gmt_validity_matches_int_valid",
    "modal_faithfulness_theory", "modal_to_deep",
    "intuitionistic_faithfulness_theory", "int_to_deep",
    "conditional_faithfulness_theory", "counterfactual_to_deep",
    "relevant_faithfulness_theory", "rel_to_deep",
]
