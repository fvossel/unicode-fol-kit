r"""Deep + maximal-shallow + minimal-shallow embeddings of **intuitionistic
propositional logic** (Kripke semantics), with machine-checked faithfulness proofs.

The accessibility relation is a preorder ``\<le>`` (``preorder``) and the valuation is
persistent (``monotone``); ``\<rightarrow>`` and ``\<not>`` quantify over ``\<le>``-successors, matching
the toolkit's :func:`unicode_fol_kit.semantics.intuitionistic.int_valid`. As in the
modal case, ``faithful1a/1b/2/3`` relate the three embeddings; here ``sound_min``
carries the two frame hypotheses (the minimal embedding fixes ``\<le>`` and ``V`` as
metalogical ``consts``, so their preorder/persistence must be assumed, not derived).
"""

from typing import Optional

from unicode_fol_kit.fol.nodes import Node, Not, And, Or, Implies, Iff
from ._common import AtomConsts, encode_deep, wrap_theory, formula_section

# --------------------------------------------------------------------------- #
# Verified theory body (checked verbatim by the Isabelle-gated tests).
# --------------------------------------------------------------------------- #

_INT_BODY = r'''typedecl w  \<comment> \<open>worlds\<close>
typedecl s  \<comment> \<open>signature: propositional symbols (shared by all three embeddings)\<close>
type_synonym wset = "w \<Rightarrow> bool"
type_synonym acc  = "w \<Rightarrow> w \<Rightarrow> bool"    \<comment> \<open>the accessibility preorder \<le>\<close>
type_synonym val  = "s \<Rightarrow> w \<Rightarrow> bool"

definition preorder :: "acc \<Rightarrow> bool" where
  "preorder L \<equiv> (\<forall>x. L x x) \<and> (\<forall>x y z. L x y \<longrightarrow> L y z \<longrightarrow> L x z)"
definition monotone :: "acc \<Rightarrow> val \<Rightarrow> bool" where
  "monotone L V \<equiv> \<forall>p x y. L x y \<longrightarrow> V p x \<longrightarrow> V p y"

section \<open>Deep embedding: object syntax as a datatype + recursive truth\<close>

datatype ipl =
    Atm s | TopD | BotD
  | NegD ipl | AndD ipl ipl | OrD ipl ipl | ImpD ipl ipl | IffD ipl ipl

primrec truthD :: "wset \<Rightarrow> acc \<Rightarrow> val \<Rightarrow> w \<Rightarrow> ipl \<Rightarrow> bool" where
  "truthD W L V x (Atm p)    = V p x"
| "truthD W L V x TopD       = True"
| "truthD W L V x BotD       = False"
| "truthD W L V x (AndD f g) = (truthD W L V x f \<and> truthD W L V x g)"
| "truthD W L V x (OrD f g)  = (truthD W L V x f \<or> truthD W L V x g)"
| "truthD W L V x (NegD f)   = (\<forall>y. L x y \<longrightarrow> \<not> truthD W L V y f)"
| "truthD W L V x (ImpD f g) = (\<forall>y. L x y \<longrightarrow> truthD W L V y f \<longrightarrow> truthD W L V y g)"
| "truthD W L V x (IffD f g) = ((\<forall>y. L x y \<longrightarrow> truthD W L V y f \<longrightarrow> truthD W L V y g)
                              \<and> (\<forall>y. L x y \<longrightarrow> truthD W L V y g \<longrightarrow> truthD W L V y f))"

definition validD :: "ipl \<Rightarrow> bool" where
  "validD f \<equiv> \<forall>W L V. preorder L \<longrightarrow> monotone L V \<longrightarrow> (\<forall>x. W x \<longrightarrow> truthD W L V x f)"

section \<open>Maximal (heavyweight) shallow embedding: every parameter explicit\<close>

type_synonym sigma = "wset \<Rightarrow> acc \<Rightarrow> val \<Rightarrow> w \<Rightarrow> bool"
definition AtmS :: "s \<Rightarrow> sigma" where "AtmS p \<equiv> \<lambda>W L V x. V p x"
definition TopS :: "sigma" where "TopS \<equiv> \<lambda>W L V x. True"
definition BotS :: "sigma" where "BotS \<equiv> \<lambda>W L V x. False"
definition AndS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "AndS f g \<equiv> \<lambda>W L V x. f W L V x \<and> g W L V x"
definition OrS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "OrS f g \<equiv> \<lambda>W L V x. f W L V x \<or> g W L V x"
definition NegS :: "sigma \<Rightarrow> sigma" where
  "NegS f \<equiv> \<lambda>W L V x. \<forall>y. L x y \<longrightarrow> \<not> f W L V y"
definition ImpS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "ImpS f g \<equiv> \<lambda>W L V x. \<forall>y. L x y \<longrightarrow> f W L V y \<longrightarrow> g W L V y"
definition IffS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "IffS f g \<equiv> \<lambda>W L V x. (\<forall>y. L x y \<longrightarrow> f W L V y \<longrightarrow> g W L V y)
                       \<and> (\<forall>y. L x y \<longrightarrow> g W L V y \<longrightarrow> f W L V y)"
definition validS :: "sigma \<Rightarrow> bool" where
  "validS f \<equiv> \<forall>W L V. preorder L \<longrightarrow> monotone L V \<longrightarrow> (\<forall>x. W x \<longrightarrow> f W L V x)"

section \<open>Minimal (lightweight) shallow embedding: \<le>, V fixed as metalogical consts\<close>

consts Leq :: "acc"
consts Vval :: "val"
type_synonym tau = "w \<Rightarrow> bool"
definition AtmM :: "s \<Rightarrow> tau" where "AtmM p \<equiv> \<lambda>x. Vval p x"
definition TopM :: "tau" where "TopM \<equiv> \<lambda>x. True"
definition BotM :: "tau" where "BotM \<equiv> \<lambda>x. False"
definition AndM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "AndM f g \<equiv> \<lambda>x. f x \<and> g x"
definition OrM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "OrM f g \<equiv> \<lambda>x. f x \<or> g x"
definition NegM :: "tau \<Rightarrow> tau" where "NegM f \<equiv> \<lambda>x. \<forall>y. Leq x y \<longrightarrow> \<not> f y"
definition ImpM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where
  "ImpM f g \<equiv> \<lambda>x. \<forall>y. Leq x y \<longrightarrow> f y \<longrightarrow> g y"
definition IffM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where
  "IffM f g \<equiv> \<lambda>x. (\<forall>y. Leq x y \<longrightarrow> f y \<longrightarrow> g y) \<and> (\<forall>y. Leq x y \<longrightarrow> g y \<longrightarrow> f y)"
definition validM :: "tau \<Rightarrow> bool" where "validM f \<equiv> \<forall>x. f x"

section \<open>Mappings between the embeddings\<close>

primrec dpToMax :: "ipl \<Rightarrow> sigma" where
  "dpToMax (Atm p)    = AtmS p"
| "dpToMax TopD       = TopS"
| "dpToMax BotD       = BotS"
| "dpToMax (NegD f)   = NegS (dpToMax f)"
| "dpToMax (AndD f g) = AndS (dpToMax f) (dpToMax g)"
| "dpToMax (OrD f g)  = OrS (dpToMax f) (dpToMax g)"
| "dpToMax (ImpD f g) = ImpS (dpToMax f) (dpToMax g)"
| "dpToMax (IffD f g) = IffS (dpToMax f) (dpToMax g)"

primrec dpToMin :: "ipl \<Rightarrow> tau" where
  "dpToMin (Atm p)    = AtmM p"
| "dpToMin TopD       = TopM"
| "dpToMin BotD       = BotM"
| "dpToMin (NegD f)   = NegM (dpToMin f)"
| "dpToMin (AndD f g) = AndM (dpToMin f) (dpToMin g)"
| "dpToMin (OrD f g)  = OrM (dpToMin f) (dpToMin g)"
| "dpToMin (ImpD f g) = ImpM (dpToMin f) (dpToMin g)"
| "dpToMin (IffD f g) = IffM (dpToMin f) (dpToMin g)"

section \<open>Faithfulness (machine-checked by Isabelle's kernel)\<close>

lemmas maxdefs = AtmS_def TopS_def BotS_def NegS_def AndS_def OrS_def ImpS_def IffS_def
lemmas mindefs = AtmM_def TopM_def BotM_def NegM_def AndM_def OrM_def ImpM_def IffM_def

text \<open>Deep truth coincides pointwise with maximal-shallow truth.\<close>
theorem faithful1a: "truthD W L V x f = dpToMax f W L V x"
  by (induct f arbitrary: x) (simp_all add: maxdefs)

text \<open>Hence deep validity coincides with maximal-shallow validity.\<close>
theorem faithful1b: "validD f = validS (dpToMax f)"
  by (simp add: validD_def validS_def faithful1a)

text \<open>Deep truth in the fixed model coincides with minimal-shallow truth.\<close>
theorem faithful2: "truthD (\<lambda>_. True) Leq Vval x f = dpToMin f x"
  by (induct f arbitrary: x) (simp_all add: mindefs)

text \<open>Maximal- and minimal-shallow truth coincide in that fixed model.\<close>
theorem faithful3: "dpToMax f (\<lambda>_. True) Leq Vval x = dpToMin f x"
  by (induct f arbitrary: x) (simp_all add: maxdefs mindefs)

text \<open>Soundness of the minimal embedding for deep validity (under the frame
      assumptions the minimal embedding fixes as consts).\<close>
theorem sound_min:
  "preorder Leq \<Longrightarrow> monotone Leq Vval \<Longrightarrow> validD f \<Longrightarrow> validM (dpToMin f)"
proof -
  assume pre: "preorder Leq" and mono: "monotone Leq Vval" and *: "validD f"
  have "truthD (\<lambda>_. True) Leq Vval x f" for x
    using * pre mono by (simp add: validD_def)
  then show "validM (dpToMin f)"
    by (simp add: validM_def faithful2)
qed'''


# --------------------------------------------------------------------------- #
# Encoder + public entry point.
# --------------------------------------------------------------------------- #

# Intuitionistic propositional connectives (no modalities; Xor is not admitted).
_CTORS = {
    Not: ("NegD", 1), And: ("AndD", 2), Or: ("OrD", 2),
    Implies: ("ImpD", 2), Iff: ("IffD", 2),
}


def int_to_deep(formula: Node, atoms: AtomConsts) -> str:
    r"""Encode a **propositional intuitionistic** formula as a deep ``ipl`` term.

    Maps ``\<not> \<and> \<or> \<rightarrow> \<leftrightarrow>`` and atoms; raises :class:`NotImplementedError` on
    modalities, ``Xor``, quantifiers, or free variables (the deep embedding is
    propositional intuitionistic).
    """
    return encode_deep(formula, atoms, _CTORS, logic="int_to_deep", allow_xor=False)


def intuitionistic_faithfulness_theory(
    theory_name: str = "IntFaithfulness",
    formula: Optional[Node] = None,
) -> str:
    r"""Emit the self-contained intuitionistic deep/maximal/minimal + faithfulness theory.

    See :func:`unicode_fol_kit.hol.deepshallow.modal.modal_faithfulness_theory`; this
    is the intuitionistic-Kripke counterpart. With a local Isabelle/HOL it is verified
    end to end by :func:`unicode_fol_kit.hol.isabelle_runner.check_theory`.
    """
    extra = ""
    if formula is not None:
        atoms = AtomConsts()
        term = int_to_deep(formula, atoms)
        extra = formula_section(term, atoms, "ipl")
    return wrap_theory(theory_name, _INT_BODY, extra)
