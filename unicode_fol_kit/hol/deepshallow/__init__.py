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
"""

from .modal import modal_faithfulness_theory, modal_to_deep
from .intuitionistic import intuitionistic_faithfulness_theory, int_to_deep
from .conditional import conditional_faithfulness_theory, counterfactual_to_deep
from .relevant import relevant_faithfulness_theory, rel_to_deep
from ._common import AtomConsts, sanitize_atom

__all__ = [
    "modal_faithfulness_theory", "modal_to_deep",
    "intuitionistic_faithfulness_theory", "int_to_deep",
    "conditional_faithfulness_theory", "counterfactual_to_deep",
    "relevant_faithfulness_theory", "rel_to_deep",
    "AtomConsts", "sanitize_atom",
]
