"""Higher-order / Isabelle / THF exporters: shallow semantical embeddings (SSE).

This subpackage *emits* Benzmüller-style shallow embeddings of the toolkit's non-fuzzy
logics into higher-order logic — as complete, self-contained problem files for an
external prover (Leo-III / Satallax on TPTP **THF**, or Isabelle/HOL theories for
Sledgehammer). The exporters only emit; a successful emission means "here is a sound
problem an external prover *may* discharge", never "decided" — first-order modal logic,
FOL and SOL are undecidable / not semi-decidable.

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
- :mod:`~unicode_fol_kit.hol.manyvalued` — three-valued K3 / LP → THF / Isabelle.
- :mod:`~unicode_fol_kit.hol.secondorder` — second-order logic → THF / Isabelle
  (native higher-order predicate quantification; standard semantics).
- :mod:`~unicode_fol_kit.hol.intuitionistic` — intuitionistic propositional logic → HOL
  via the Gödel–McKinsey–Tarski translation into S4 then the alethic SSE.
"""

from .isabelle_modal import (
    to_isabelle_modal, isabelle_modal_theory, ISABELLE_TACTICS, modal_axiom_names,
)
from .isabelle_runner import (
    find_isabelle, isabelle_available, isabelle_decide_modal, check_theory,
    IsabelleInstall, IsabelleNotAvailable, BuildResult, ModalVerdict, DEFAULT_METHODS,
)
from .thf_modal import to_thf_modal_full, thf_full_definitions, thf_full_frame_axioms
from .classical import to_thf_fol, to_isabelle_fol, to_thf_msfol, to_isabelle_msfol
from .manyvalued import (
    to_thf_k3lp, to_isabelle_k3lp,
    to_thf_k3lp_entailment, to_isabelle_k3lp_entailment, SYSTEMS,
)
from .secondorder import to_thf_so, to_isabelle_so
from .intuitionistic import (
    gmt_translate, to_thf_intuitionistic, to_isabelle_intuitionistic,
    gmt_is_s4_valid, gmt_validity_matches_int_valid,
)

__all__ = [
    "to_isabelle_modal", "isabelle_modal_theory", "ISABELLE_TACTICS",
    "modal_axiom_names",
    "find_isabelle", "isabelle_available", "isabelle_decide_modal", "check_theory",
    "IsabelleInstall", "IsabelleNotAvailable", "BuildResult", "ModalVerdict",
    "DEFAULT_METHODS",
    "to_thf_modal_full", "thf_full_definitions", "thf_full_frame_axioms",
    "to_thf_fol", "to_isabelle_fol", "to_thf_msfol", "to_isabelle_msfol",
    "to_thf_k3lp", "to_isabelle_k3lp",
    "to_thf_k3lp_entailment", "to_isabelle_k3lp_entailment", "SYSTEMS",
    "to_thf_so", "to_isabelle_so",
    "gmt_translate", "to_thf_intuitionistic", "to_isabelle_intuitionistic",
    "gmt_is_s4_valid", "gmt_validity_matches_int_valid",
]
