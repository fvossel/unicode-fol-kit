r"""Deep + maximal-shallow + minimal-shallow embeddings of **Lewis counterfactual
(sphere) logic**, with machine-checked faithfulness proofs.

The Boolean base is classical (per-world), and the counterfactual ``A \<box>\<rightarrow> B`` is
read over a system of spheres ``Sph x S`` (``S`` is a sphere of worlds around ``x``,
innermost = closest) with Lewis's truth condition — vacuously true if no sphere holds
an ``A``-world, else some sphere holds an ``A``-world and all its ``A``-worlds are
``B``-worlds — matching :func:`unicode_fol_kit.semantics.conditional.would`. Validity
ranges over ``nested`` sphere systems (any two spheres of a world are
\<subseteq>-comparable), the property Lewis's nested spheres have by construction; that
is the weakest sphere logic **V**. The dual "might" ``A \<diamond>\<rightarrow> B`` is
``\<not>(A \<box>\<rightarrow> \<not>B)``.

**Which sphere class this is** — and how it differs from the decision routes. ``validD``
/ ``validS`` here fix ``nested Sp`` and nothing more, so they denote the class
:data:`~unicode_fol_kit.semantics.conditional.CENTERING_LEVELS`'s ``"none"`` names, i.e.
Lewis's **V**. :func:`~unicode_fol_kit.semantics.conditional.cf_valid` and
:func:`~unicode_fol_kit.hol.isabelle_runner.isabelle_decide_counterfactual` default to
``"weak"`` (**VW**) instead, because modus ponens for ``\<box>\<rightarrow>`` fails in V.
That difference is deliberate: what is machine-checked in this module is the *faithfulness*
of the three embeddings to each other, which is a statement about the truth condition and
holds at every centering level — adding a centering premise here would constrain the
sphere systems without changing anything the faithfulness theorems say. Do not read a
``validD`` verdict as a verdict about the logic ``cf_valid`` decides.

The deep term is built from an antecedent/consequent **pair** rather than from a single
formula node: the encoder predates the ``Would`` / ``Might`` AST nodes and mirrors the
argument form of ``would`` / ``might``, whose propositional-only contract it shares.
"""

from typing import Optional

from unicode_fol_kit.fol.nodes import Node, Not, And, Or, Implies, Iff
from ._common import AtomConsts, encode_deep, wrap_theory, formula_section

# --------------------------------------------------------------------------- #
# Verified theory body (checked verbatim by the Isabelle-gated tests).
# --------------------------------------------------------------------------- #

_COND_BODY = r'''typedecl w  \<comment> \<open>worlds\<close>
typedecl s  \<comment> \<open>signature: propositional symbols (shared by all three embeddings)\<close>
type_synonym wset = "w \<Rightarrow> bool"
type_synonym sph  = "w \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> bool"   \<comment> \<open>Sph x S: S is a sphere around x\<close>
type_synonym val  = "s \<Rightarrow> w \<Rightarrow> bool"

definition nested :: "sph \<Rightarrow> bool" where
  "nested Sp \<equiv> \<forall>x S T. Sp x S \<longrightarrow> Sp x T \<longrightarrow> (\<forall>u. S u \<longrightarrow> T u) \<or> (\<forall>u. T u \<longrightarrow> S u)"

section \<open>Deep embedding: object syntax as a datatype + recursive truth\<close>

datatype cpl =
    Atm s | TopD | BotD
  | NegD cpl | AndD cpl cpl | OrD cpl cpl | ImpD cpl cpl | IffD cpl cpl
  | CondD cpl cpl

primrec truthD :: "wset \<Rightarrow> sph \<Rightarrow> val \<Rightarrow> w \<Rightarrow> cpl \<Rightarrow> bool" where
  "truthD W Sp V x (Atm p)    = V p x"
| "truthD W Sp V x TopD       = True"
| "truthD W Sp V x BotD       = False"
| "truthD W Sp V x (NegD f)   = (\<not> truthD W Sp V x f)"
| "truthD W Sp V x (AndD f g) = (truthD W Sp V x f \<and> truthD W Sp V x g)"
| "truthD W Sp V x (OrD f g)  = (truthD W Sp V x f \<or> truthD W Sp V x g)"
| "truthD W Sp V x (ImpD f g) = (truthD W Sp V x f \<longrightarrow> truthD W Sp V x g)"
| "truthD W Sp V x (IffD f g) = (truthD W Sp V x f = truthD W Sp V x g)"
| "truthD W Sp V x (CondD f g) =
     ((\<exists>S. Sp x S \<and> (\<exists>u. S u \<and> truthD W Sp V u f)
                  \<and> (\<forall>u. S u \<longrightarrow> truthD W Sp V u f \<longrightarrow> truthD W Sp V u g))
      \<or> (\<forall>S. Sp x S \<longrightarrow> (\<forall>u. S u \<longrightarrow> \<not> truthD W Sp V u f)))"

definition validD :: "cpl \<Rightarrow> bool" where
  "validD f \<equiv> \<forall>W Sp V. nested Sp \<longrightarrow> (\<forall>x. W x \<longrightarrow> truthD W Sp V x f)"

section \<open>Maximal (heavyweight) shallow embedding: every parameter explicit\<close>

type_synonym sigma = "wset \<Rightarrow> sph \<Rightarrow> val \<Rightarrow> w \<Rightarrow> bool"
definition AtmS :: "s \<Rightarrow> sigma" where "AtmS p \<equiv> \<lambda>W Sp V x. V p x"
definition TopS :: "sigma" where "TopS \<equiv> \<lambda>W Sp V x. True"
definition BotS :: "sigma" where "BotS \<equiv> \<lambda>W Sp V x. False"
definition NegS :: "sigma \<Rightarrow> sigma" where "NegS f \<equiv> \<lambda>W Sp V x. \<not> f W Sp V x"
definition AndS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "AndS f g \<equiv> \<lambda>W Sp V x. f W Sp V x \<and> g W Sp V x"
definition OrS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "OrS f g \<equiv> \<lambda>W Sp V x. f W Sp V x \<or> g W Sp V x"
definition ImpS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "ImpS f g \<equiv> \<lambda>W Sp V x. f W Sp V x \<longrightarrow> g W Sp V x"
definition IffS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "IffS f g \<equiv> \<lambda>W Sp V x. f W Sp V x = g W Sp V x"
definition CondS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "CondS f g \<equiv> \<lambda>W Sp V x.
     (\<exists>S. Sp x S \<and> (\<exists>u. S u \<and> f W Sp V u)
                 \<and> (\<forall>u. S u \<longrightarrow> f W Sp V u \<longrightarrow> g W Sp V u))
     \<or> (\<forall>S. Sp x S \<longrightarrow> (\<forall>u. S u \<longrightarrow> \<not> f W Sp V u))"
definition validS :: "sigma \<Rightarrow> bool" where
  "validS f \<equiv> \<forall>W Sp V. nested Sp \<longrightarrow> (\<forall>x. W x \<longrightarrow> f W Sp V x)"

section \<open>Minimal (lightweight) shallow embedding: Sph, V fixed as metalogical consts\<close>

consts Sel :: "sph"
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
definition CondM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where
  "CondM f g \<equiv> \<lambda>x.
     (\<exists>S. Sel x S \<and> (\<exists>u. S u \<and> f u) \<and> (\<forall>u. S u \<longrightarrow> f u \<longrightarrow> g u))
     \<or> (\<forall>S. Sel x S \<longrightarrow> (\<forall>u. S u \<longrightarrow> \<not> f u))"
definition validM :: "tau \<Rightarrow> bool" where "validM f \<equiv> \<forall>x. f x"

section \<open>Mappings between the embeddings\<close>

primrec dpToMax :: "cpl \<Rightarrow> sigma" where
  "dpToMax (Atm p)    = AtmS p"
| "dpToMax TopD       = TopS"
| "dpToMax BotD       = BotS"
| "dpToMax (NegD f)   = NegS (dpToMax f)"
| "dpToMax (AndD f g) = AndS (dpToMax f) (dpToMax g)"
| "dpToMax (OrD f g)  = OrS (dpToMax f) (dpToMax g)"
| "dpToMax (ImpD f g) = ImpS (dpToMax f) (dpToMax g)"
| "dpToMax (IffD f g) = IffS (dpToMax f) (dpToMax g)"
| "dpToMax (CondD f g) = CondS (dpToMax f) (dpToMax g)"

primrec dpToMin :: "cpl \<Rightarrow> tau" where
  "dpToMin (Atm p)    = AtmM p"
| "dpToMin TopD       = TopM"
| "dpToMin BotD       = BotM"
| "dpToMin (NegD f)   = NegM (dpToMin f)"
| "dpToMin (AndD f g) = AndM (dpToMin f) (dpToMin g)"
| "dpToMin (OrD f g)  = OrM (dpToMin f) (dpToMin g)"
| "dpToMin (ImpD f g) = ImpM (dpToMin f) (dpToMin g)"
| "dpToMin (IffD f g) = IffM (dpToMin f) (dpToMin g)"
| "dpToMin (CondD f g) = CondM (dpToMin f) (dpToMin g)"

section \<open>Faithfulness (machine-checked by Isabelle's kernel)\<close>

lemmas maxdefs = AtmS_def TopS_def BotS_def NegS_def AndS_def OrS_def
                 ImpS_def IffS_def CondS_def
lemmas mindefs = AtmM_def TopM_def BotM_def NegM_def AndM_def OrM_def
                 ImpM_def IffM_def CondM_def

text \<open>Deep truth coincides pointwise with maximal-shallow truth.\<close>
theorem faithful1a: "truthD W Sp V x f = dpToMax f W Sp V x"
  by (induct f arbitrary: x) (simp_all add: maxdefs)

text \<open>Hence deep validity coincides with maximal-shallow validity.\<close>
theorem faithful1b: "validD f = validS (dpToMax f)"
  by (simp add: validD_def validS_def faithful1a)

text \<open>Deep truth in the fixed model coincides with minimal-shallow truth.\<close>
theorem faithful2: "truthD (\<lambda>_. True) Sel Vval x f = dpToMin f x"
  by (induct f arbitrary: x) (simp_all add: mindefs)

text \<open>Maximal- and minimal-shallow truth coincide in that fixed model.\<close>
theorem faithful3: "dpToMax f (\<lambda>_. True) Sel Vval x = dpToMin f x"
  by (induct f arbitrary: x) (simp_all add: maxdefs mindefs)

text \<open>Soundness of the minimal embedding for deep validity (under the nesting
      assumption the minimal embedding fixes as a const).\<close>
theorem sound_min: "nested Sel \<Longrightarrow> validD f \<Longrightarrow> validM (dpToMin f)"
proof -
  assume ne: "nested Sel" and *: "validD f"
  have "truthD (\<lambda>_. True) Sel Vval x f" for x
    using * ne by (simp add: validD_def)
  then show "validM (dpToMin f)"
    by (simp add: validM_def faithful2)
qed'''


# --------------------------------------------------------------------------- #
# Encoder + public entry point.
# --------------------------------------------------------------------------- #

# Boolean base (classical, per world); the counterfactual is built explicitly from
# an antecedent/consequent pair — there is no counterfactual node in the AST.
_BOOL_CTORS = {
    Not: ("NegD", 1), And: ("AndD", 2), Or: ("OrD", 2),
    Implies: ("ImpD", 2), Iff: ("IffD", 2),
}


def counterfactual_to_deep(antecedent: Node, consequent: Node,
                           atoms: AtomConsts, kind: str = "would") -> str:
    r"""Encode a counterfactual as a deep ``cpl`` term.

    ``kind="would"`` builds ``(CondD <a> <b>)`` (``a \<box>\<rightarrow> b``); ``kind="might"``
    builds ``(NegD (CondD <a> (NegD <b>)))`` (``a \<diamond>\<rightarrow> b \<equiv> \<not>(a \<box>\<rightarrow> \<not>b)``).
    Antecedent and consequent are **propositional** (atoms + Boolean connectives),
    matching :func:`unicode_fol_kit.semantics.conditional.would`.
    """
    a = encode_deep(antecedent, atoms, _BOOL_CTORS, logic="counterfactual_to_deep")
    b = encode_deep(consequent, atoms, _BOOL_CTORS, logic="counterfactual_to_deep")
    if kind == "would":
        return f"(CondD {a} {b})"
    if kind == "might":
        return f"(NegD (CondD {a} (NegD {b})))"
    raise ValueError(f"counterfactual_to_deep: kind must be 'would' or 'might', got {kind!r}.")


def conditional_faithfulness_theory(
    theory_name: str = "CondFaithfulness",
    antecedent: Optional[Node] = None,
    consequent: Optional[Node] = None,
    kind: str = "would",
) -> str:
    r"""Emit the self-contained Lewis-conditional deep/maximal/minimal + faithfulness theory.

    When both ``antecedent`` and ``consequent`` are given, the corresponding
    counterfactual (``kind`` ``"would"`` / ``"might"``) is appended as
    ``definition example :: cpl``. With a local Isabelle/HOL the theory is verified
    end to end by :func:`unicode_fol_kit.hol.isabelle_runner.check_theory`.
    """
    extra = ""
    if antecedent is not None and consequent is not None:
        atoms = AtomConsts()
        term = counterfactual_to_deep(antecedent, consequent, atoms, kind=kind)
        extra = formula_section(term, atoms, "cpl")
    elif (antecedent is None) != (consequent is None):
        raise ValueError(
            "conditional_faithfulness_theory: pass both antecedent and consequent, or neither.")
    return wrap_theory(theory_name, _COND_BODY, extra)
