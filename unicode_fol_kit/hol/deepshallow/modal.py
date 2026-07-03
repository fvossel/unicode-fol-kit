r"""Deep + maximal-shallow + minimal-shallow embeddings of **propositional modal
logic** K, with machine-checked faithfulness proofs (the Benzmüller construction).

The emitted theory is self-contained and, with a local Isabelle/HOL, verifies end
to end: ``faithful1a/1b`` relate the deep and maximal-shallow embeddings,
``faithful2/3`` relate them to the minimal-shallow embedding in the fixed model
``(W := \<lambda>_. True, R := Racc, V := Vval)``, and ``sound_min`` records that the
minimal embedding is sound for deep validity. Each proof is a one-line
``induct`` — see :func:`modal_faithfulness_theory`.

The accessibility relation ``R`` is left arbitrary, so faithfulness holds for the
base logic K (and hence, a fortiori, under any frame conditions). Deciding
validity *under a specific frame* is the job of the quantified minimal embedding in
:mod:`unicode_fol_kit.hol.isabelle_modal`; this module is about the three
embeddings and the faithful bridges between them.
"""

from typing import Optional

from unicode_fol_kit.fol.nodes import (
    Node, Not, And, Or, Implies, Iff, Box, Diamond,
)
from ._common import AtomConsts, encode_deep, wrap_theory, formula_section

# --------------------------------------------------------------------------- #
# The verified theory body (everything between ``begin`` and ``end``).
#
# This text is checked verbatim by the Isabelle-gated tests: exit 0 from
# ``check_theory`` means Isabelle's kernel discharged all five faithfulness
# theorems. Do not edit a clause without re-running that check — the ``induct``
# proofs depend on the exact operator definitions and the ``maxdefs`` / ``mindefs``
# simp bundles.
# --------------------------------------------------------------------------- #

_MODAL_BODY = r'''typedecl w  \<comment> \<open>worlds\<close>
typedecl s  \<comment> \<open>signature: propositional symbols (shared by all three embeddings)\<close>
type_synonym wset = "w \<Rightarrow> bool"        \<comment> \<open>a set of worlds W\<close>
type_synonym acc  = "w \<Rightarrow> w \<Rightarrow> bool"   \<comment> \<open>accessibility relation R\<close>
type_synonym val  = "s \<Rightarrow> w \<Rightarrow> bool"    \<comment> \<open>valuation V\<close>

section \<open>Deep embedding: object syntax as a datatype + recursive truth\<close>

datatype pml =
    Atm s | TopD | BotD
  | NegD pml | AndD pml pml | OrD pml pml | ImpD pml pml | IffD pml pml
  | BoxD pml | DiaD pml

primrec truthD :: "wset \<Rightarrow> acc \<Rightarrow> val \<Rightarrow> w \<Rightarrow> pml \<Rightarrow> bool" where
  "truthD W R V x (Atm p)    = V p x"
| "truthD W R V x TopD       = True"
| "truthD W R V x BotD       = False"
| "truthD W R V x (NegD f)   = (\<not> truthD W R V x f)"
| "truthD W R V x (AndD f g) = (truthD W R V x f \<and> truthD W R V x g)"
| "truthD W R V x (OrD f g)  = (truthD W R V x f \<or> truthD W R V x g)"
| "truthD W R V x (ImpD f g) = (truthD W R V x f \<longrightarrow> truthD W R V x g)"
| "truthD W R V x (IffD f g) = (truthD W R V x f = truthD W R V x g)"
| "truthD W R V x (BoxD f)   = (\<forall>y. R x y \<longrightarrow> truthD W R V y f)"
| "truthD W R V x (DiaD f)   = (\<exists>y. R x y \<and> truthD W R V y f)"

definition validD :: "pml \<Rightarrow> bool" where
  "validD f \<equiv> \<forall>W R V. \<forall>x. W x \<longrightarrow> truthD W R V x f"

section \<open>Maximal (heavyweight) shallow embedding: every parameter explicit\<close>

type_synonym sigma = "wset \<Rightarrow> acc \<Rightarrow> val \<Rightarrow> w \<Rightarrow> bool"
definition AtmS :: "s \<Rightarrow> sigma" where "AtmS p \<equiv> \<lambda>W R V x. V p x"
definition TopS :: "sigma" where "TopS \<equiv> \<lambda>W R V x. True"
definition BotS :: "sigma" where "BotS \<equiv> \<lambda>W R V x. False"
definition NegS :: "sigma \<Rightarrow> sigma" where "NegS f \<equiv> \<lambda>W R V x. \<not> f W R V x"
definition AndS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "AndS f g \<equiv> \<lambda>W R V x. f W R V x \<and> g W R V x"
definition OrS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "OrS f g \<equiv> \<lambda>W R V x. f W R V x \<or> g W R V x"
definition ImpS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "ImpS f g \<equiv> \<lambda>W R V x. f W R V x \<longrightarrow> g W R V x"
definition IffS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "IffS f g \<equiv> \<lambda>W R V x. f W R V x = g W R V x"
definition BoxS :: "sigma \<Rightarrow> sigma" where
  "BoxS f \<equiv> \<lambda>W R V x. \<forall>y. R x y \<longrightarrow> f W R V y"
definition DiaS :: "sigma \<Rightarrow> sigma" where
  "DiaS f \<equiv> \<lambda>W R V x. \<exists>y. R x y \<and> f W R V y"
definition validS :: "sigma \<Rightarrow> bool" where
  "validS f \<equiv> \<forall>W R V. \<forall>x. W x \<longrightarrow> f W R V x"

section \<open>Minimal (lightweight) shallow embedding: R, V fixed as metalogical consts\<close>

consts Racc :: "acc"
consts Vval :: "val"
type_synonym tau = "w \<Rightarrow> bool"
definition AtmM :: "s \<Rightarrow> tau" where "AtmM p \<equiv> \<lambda>x. Vval p x"
definition TopM :: "tau" where "TopM \<equiv> \<lambda>x. True"
definition BotM :: "tau" where "BotM \<equiv> \<lambda>x. False"
definition NegM :: "tau \<Rightarrow> tau" where "NegM f \<equiv> \<lambda>x. \<not> f x"
definition AndM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "AndM f g \<equiv> \<lambda>x. f x \<and> g x"
definition OrM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "OrM f g \<equiv> \<lambda>x. f x \<or> g x"
definition ImpM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "ImpM f g \<equiv> \<lambda>x. f x \<longrightarrow> g x"
definition IffM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "IffM f g \<equiv> \<lambda>x. f x = g x"
definition BoxM :: "tau \<Rightarrow> tau" where "BoxM f \<equiv> \<lambda>x. \<forall>y. Racc x y \<longrightarrow> f y"
definition DiaM :: "tau \<Rightarrow> tau" where "DiaM f \<equiv> \<lambda>x. \<exists>y. Racc x y \<and> f y"
definition validM :: "tau \<Rightarrow> bool" where "validM f \<equiv> \<forall>x. f x"

section \<open>Mappings between the embeddings\<close>

primrec dpToMax :: "pml \<Rightarrow> sigma" where
  "dpToMax (Atm p)    = AtmS p"
| "dpToMax TopD       = TopS"
| "dpToMax BotD       = BotS"
| "dpToMax (NegD f)   = NegS (dpToMax f)"
| "dpToMax (AndD f g) = AndS (dpToMax f) (dpToMax g)"
| "dpToMax (OrD f g)  = OrS (dpToMax f) (dpToMax g)"
| "dpToMax (ImpD f g) = ImpS (dpToMax f) (dpToMax g)"
| "dpToMax (IffD f g) = IffS (dpToMax f) (dpToMax g)"
| "dpToMax (BoxD f)   = BoxS (dpToMax f)"
| "dpToMax (DiaD f)   = DiaS (dpToMax f)"

primrec dpToMin :: "pml \<Rightarrow> tau" where
  "dpToMin (Atm p)    = AtmM p"
| "dpToMin TopD       = TopM"
| "dpToMin BotD       = BotM"
| "dpToMin (NegD f)   = NegM (dpToMin f)"
| "dpToMin (AndD f g) = AndM (dpToMin f) (dpToMin g)"
| "dpToMin (OrD f g)  = OrM (dpToMin f) (dpToMin g)"
| "dpToMin (ImpD f g) = ImpM (dpToMin f) (dpToMin g)"
| "dpToMin (IffD f g) = IffM (dpToMin f) (dpToMin g)"
| "dpToMin (BoxD f)   = BoxM (dpToMin f)"
| "dpToMin (DiaD f)   = DiaM (dpToMin f)"

section \<open>Faithfulness (machine-checked by Isabelle's kernel)\<close>

lemmas maxdefs = AtmS_def TopS_def BotS_def NegS_def AndS_def OrS_def
                 ImpS_def IffS_def BoxS_def DiaS_def
lemmas mindefs = AtmM_def TopM_def BotM_def NegM_def AndM_def OrM_def
                 ImpM_def IffM_def BoxM_def DiaM_def

text \<open>Deep truth coincides pointwise with maximal-shallow truth.\<close>
theorem faithful1a: "truthD W R V x f = dpToMax f W R V x"
  by (induct f arbitrary: x) (simp_all add: maxdefs)

text \<open>Hence deep validity coincides with maximal-shallow validity.\<close>
theorem faithful1b: "validD f = validS (dpToMax f)"
  by (simp add: validD_def validS_def faithful1a)

text \<open>Deep truth in the fixed model coincides with minimal-shallow truth.\<close>
theorem faithful2: "truthD (\<lambda>_. True) Racc Vval x f = dpToMin f x"
  by (induct f arbitrary: x) (simp_all add: mindefs)

text \<open>Maximal- and minimal-shallow truth coincide in that fixed model.\<close>
theorem faithful3: "dpToMax f (\<lambda>_. True) Racc Vval x = dpToMin f x"
  by (induct f arbitrary: x) (simp_all add: maxdefs mindefs)

text \<open>Soundness of the minimal embedding for deep validity.\<close>
theorem sound_min: "validD f \<Longrightarrow> validM (dpToMin f)"
proof -
  assume *: "validD f"
  have "truthD (\<lambda>_. True) Racc Vval x f" for x
    using * by (simp add: validD_def)
  then show "validM (dpToMin f)"
    by (simp add: validM_def faithful2)
qed'''


# --------------------------------------------------------------------------- #
# Encoder:  toolkit modal AST  ->  deep ``pml`` term.
# --------------------------------------------------------------------------- #

# Node type -> (deep constructor, arity). Xor desugars to NegD (IffD ...).
_CTORS = {
    Not: ("NegD", 1), And: ("AndD", 2), Or: ("OrD", 2),
    Implies: ("ImpD", 2), Iff: ("IffD", 2),
    Box: ("BoxD", 1), Diamond: ("DiaD", 1),
}


def modal_to_deep(formula: Node, atoms: AtomConsts) -> str:
    r"""Encode a **propositional** modal formula as a deep ``pml`` term.

    Each distinct ground atom becomes a propositional symbol constant of type ``s``
    (collected into ``atoms``); connectives map to the ``pml`` constructors and
    ``Xor`` desugars to ``NegD (IffD ...)``. Raises :class:`NotImplementedError` if
    the formula is genuinely first-order (contains a quantifier or a variable) — the
    deep embedding is propositional; use :mod:`unicode_fol_kit.hol.isabelle_modal`
    for the quantified fragment.
    """
    return encode_deep(formula, atoms, _CTORS, logic="modal_to_deep")


# --------------------------------------------------------------------------- #
# Public entry points.
# --------------------------------------------------------------------------- #

def modal_faithfulness_theory(
    theory_name: str = "ModalFaithfulness",
    formula: Optional[Node] = None,
) -> str:
    r"""Emit the self-contained modal deep/maximal/minimal + faithfulness theory.

    The returned string is a full ``theory <theory_name> imports Main begin ... end``
    containing the three embeddings and the five faithfulness theorems, each closed
    by Isabelle. With a local Isabelle/HOL it is verified end to end by
    :func:`unicode_fol_kit.hol.isabelle_runner.check_theory`.

    Args:
        theory_name: the Isabelle theory / file name (a legal identifier).
        formula: an optional **propositional** modal formula. When given, its deep
            encoding is appended as ``definition example :: pml`` (with ``consts`` for
            its atoms), so the certificate is grounded in a concrete formula and the
            faithfulness theorems specialise to it.

    Returns:
        The theory text (newline-terminated).
    """
    extra = ""
    if formula is not None:
        atoms = AtomConsts()
        term = modal_to_deep(formula, atoms)
        extra = formula_section(term, atoms, "pml")
    return wrap_theory(theory_name, _MODAL_BODY, extra)
