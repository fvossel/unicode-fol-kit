r"""Deep + maximal-shallow + minimal-shallow HOL embeddings with faithfulness proofs.

Reproduces, per non-classical object logic, the three faithful HOL embeddings of
Benzmüller, *Faithful Logic Embeddings in HOL — Deep and Shallow*
(arXiv:2502.19311v3), together with the **machine-checked faithfulness proofs**
relating them. See :mod:`unicode_fol_kit.hol.deepshallow._common` for the shared
construction and honesty notes.

Currently provided (Tier 1 — worlds-based logics that carry the deep/maximal/minimal
+ faithfulness scheme cleanly):

- :mod:`~unicode_fol_kit.hol.deepshallow.modal` — propositional modal logic K.
- :mod:`~unicode_fol_kit.hol.deepshallow.intuitionistic` — intuitionistic
  propositional logic (Kripke semantics).
- :mod:`~unicode_fol_kit.hol.deepshallow.conditional` — Lewis counterfactual
  (sphere) logic.
- :mod:`~unicode_fol_kit.hol.deepshallow.relevant` — relevant logic B
  (simplified Routley–Meyer semantics).

Tier 2 (K, constant domain only) — the first *quantified* member of the family,
with a genuinely binder-carrying deep embedding (de Bruijn-indexed object
variables) rather than a propositional/schematic syntax tree:

- :mod:`~unicode_fol_kit.hol.deepshallow.qml` — quantified modal logic, scoped to
  the base frame K, the CONSTANT domain regime, and the alethic ``□``/``◇``
  modalities only. Every other frame, domain regime, agent-indexed/temporal/
  deontic operator, equality and function term is refused by name — see the
  module docstring and :mod:`unicode_fol_kit.hol.isabelle_modal` for those.
"""

from .modal import modal_faithfulness_theory, modal_to_deep
from .intuitionistic import intuitionistic_faithfulness_theory, int_to_deep
from .conditional import conditional_faithfulness_theory, counterfactual_to_deep
from .relevant import relevant_faithfulness_theory, rel_to_deep
from .qml import qml_deep_faithfulness_theory, qml_to_deep
from ._common import AtomConsts, sanitize_atom

__all__ = [
    "modal_faithfulness_theory", "modal_to_deep",
    "intuitionistic_faithfulness_theory", "int_to_deep",
    "conditional_faithfulness_theory", "counterfactual_to_deep",
    "relevant_faithfulness_theory", "rel_to_deep",
    "qml_deep_faithfulness_theory", "qml_to_deep",
    "AtomConsts", "sanitize_atom",
]
